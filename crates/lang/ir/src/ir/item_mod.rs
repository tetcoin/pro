// Copyright 2018-2021 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    ir,
    ir::idents_lint,
};
use core::convert::TryFrom;
use proc_macro2::{
    Ident,
    Span,
};
use quote::TokenStreamExt as _;
use std::collections::HashMap;
use syn::{
    spanned::Spanned,
    token,
};

/// The pro! module.
///
/// This is the root of all pro! smart contracts and is defined similarly to
/// a normal Rust module annotated with
/// `#[pro::contract( /* optional configuration */ )]` attribute.
///
/// It contains pro! specific items as well as normal Rust items.
///
/// # Example
///
/// ```
/// // #[pro::contract] <-- this line belongs to the pro! configuration!
/// # use core::convert::TryFrom;
/// # use pro_lang_ir as ir;
/// # <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(syn::parse_quote! {
/// mod my_contract {
///     #[pro(storage)]
///     pub struct MyStorage {
///         /* storage fields */
///     }
///
///     #[pro(event)]
///     pub struct MyEvent {
///         /* event fields */
///     }
///
///     impl MyStorage {
///         #[pro(constructor)]
///         pub fn my_constructor() -> Self {
///             /* constructor initialization */
///         }
///
///         #[pro(message)]
///         pub fn my_message(&self) {
///             /* message statements */
///         }
///     }
/// }
/// # }).unwrap();
/// ```
///
/// # Note
///
/// This type has been named after [`syn::ItemMod`] and inherits all of the
/// fields that are required for inline module definitions.
///
/// # Developer Note
///
/// Structurally the pro! `Module` mirrors an inline Rust module, for example:
///
/// ```
/// mod rust_module {
///     /* some Rust item definitions */
/// }
/// ```
///
/// If the capabilities of an inline Rust module change we have to adjust for that.
#[derive(Debug, PartialEq, Eq)]
pub struct ItemMod {
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    mod_token: token::Mod,
    ident: Ident,
    brace: token::Brace,
    items: Vec<ir::Item>,
}

impl ItemMod {
    /// Ensures that the pro! storage struct is not missing and that there are
    /// not multiple pro! storage struct definitions for the given slice of items.
    fn ensure_storage_struct_quantity(
        module_span: Span,
        items: &[ir::Item],
    ) -> Result<(), syn::Error> {
        let storage_iter = items
            .iter()
            .filter(|item| matches!(item, ir::Item::Pro(ir::ProItem::Storage(_))));
        if storage_iter.clone().next().is_none() {
            return Err(format_err!(module_span, "missing pro! storage struct",))
        }
        if storage_iter.clone().count() >= 2 {
            let mut error = format_err!(
                module_span,
                "encountered multiple pro! storage structs, expected exactly one"
            );
            for storage in storage_iter {
                error.combine(format_err!(storage, "pro! storage struct here"))
            }
            return Err(error)
        }
        Ok(())
    }

    /// Ensures that the given slice of items contains at least one pro! message.
    fn ensure_contains_message(
        module_span: Span,
        items: &[ir::Item],
    ) -> Result<(), syn::Error> {
        let found_message = items
            .iter()
            .filter_map(|item| {
                match item {
                    ir::Item::Pro(ir::ProItem::ImplBlock(item_impl)) => {
                        Some(item_impl.iter_messages())
                    }
                    _ => None,
                }
            })
            .any(|mut messages| messages.next().is_some());
        if !found_message {
            return Err(format_err!(module_span, "missing pro! message"))
        }
        Ok(())
    }

    /// Ensures that the given slice of items contains at least one pro! constructor.
    fn ensure_contains_constructor(
        module_span: Span,
        items: &[ir::Item],
    ) -> Result<(), syn::Error> {
        let found_constructor = items
            .iter()
            .filter_map(|item| {
                match item {
                    ir::Item::Pro(ir::ProItem::ImplBlock(item_impl)) => {
                        Some(item_impl.iter_constructors())
                    }
                    _ => None,
                }
            })
            .any(|mut constructors| constructors.next().is_some());
        if !found_constructor {
            return Err(format_err!(module_span, "missing pro! constructor"))
        }
        Ok(())
    }

    /// Ensures that no pro! message or constructor selectors are overlapping.
    ///
    /// # Note
    ///
    /// We differentiate between pro! message and pro! constructor selectors
    /// since they are dispatched independently from each other and thus are
    /// allowed to have overlapping selectors.
    fn ensure_no_overlapping_selectors(items: &[ir::Item]) -> Result<(), syn::Error> {
        let mut messages = <HashMap<ir::Selector, &ir::Message>>::new();
        let mut constructors = <HashMap<ir::Selector, &ir::Constructor>>::new();
        for item_impl in items
            .iter()
            .filter_map(ir::Item::map_pro_item)
            .filter_map(ir::ProItem::filter_map_impl_block)
        {
            use std::collections::hash_map::Entry;
            /// Kind is either `"message"` or `"constructor"`.
            fn compose_error(
                first_span: Span,
                second_span: Span,
                selector: ir::Selector,
                kind: &str,
            ) -> syn::Error {
                use crate::error::ExtError as _;
                format_err!(
                    second_span,
                    "encountered pro! {}s with overlapping selectors (= {:02X?})\n\
                     hint: use #[pro(selector = \"0x...\")] on the callable or \
                     #[pro(namespace = \"...\")] on the implementation block to \
                     disambiguate overlapping selectors.",
                    kind,
                    selector.as_bytes(),
                )
                .into_combine(format_err!(
                    first_span,
                    "first pro! {} with overlapping selector here",
                    kind,
                ))
            }
            for message in item_impl.iter_messages() {
                let selector = message.composed_selector();
                match messages.entry(selector) {
                    Entry::Occupied(overlap) => {
                        return Err(compose_error(
                            overlap.get().span(),
                            message.callable().span(),
                            selector,
                            "message",
                        ))
                    }
                    Entry::Vacant(vacant) => {
                        vacant.insert(message.callable());
                    }
                }
            }
            for constructor in item_impl.iter_constructors() {
                let selector = constructor.composed_selector();
                match constructors.entry(selector) {
                    Entry::Occupied(overlap) => {
                        return Err(compose_error(
                            overlap.get().span(),
                            constructor.callable().span(),
                            selector,
                            "constructor",
                        ))
                    }
                    Entry::Vacant(vacant) => {
                        vacant.insert(constructor.callable());
                    }
                }
            }
        }
        Ok(())
    }
}

impl TryFrom<syn::ItemMod> for ItemMod {
    type Error = syn::Error;

    fn try_from(module: syn::ItemMod) -> Result<Self, Self::Error> {
        let module_span = module.span();
        idents_lint::ensure_no_pro_identifiers(&module)?;
        let (brace, items) = match module.content {
            Some((brace, items)) => (brace, items),
            None => {
                return Err(format_err_spanned!(
                    module,
                    "out-of-line pro! modules are not supported, use `#[pro::contract] mod name {{ ... }}`",
                ))
            }
        };
        let (pro_attrs, other_attrs) = ir::partition_attributes(module.attrs)?;
        if !pro_attrs.is_empty() {
            let mut error = format_err!(
                module_span,
                "encountered invalid pro! attributes on pro! module"
            );
            for pro_attr in pro_attrs {
                error.combine(format_err!(
                    pro_attr.span(),
                    "invalid pro! attribute on module"
                ))
            }
            return Err(error)
        }
        let items = items
            .into_iter()
            .map(<ir::Item as TryFrom<syn::Item>>::try_from)
            .collect::<Result<Vec<_>, syn::Error>>()?;
        Self::ensure_storage_struct_quantity(module_span, &items)?;
        Self::ensure_contains_message(module_span, &items)?;
        Self::ensure_contains_constructor(module_span, &items)?;
        Self::ensure_no_overlapping_selectors(&items)?;
        Ok(Self {
            attrs: other_attrs,
            vis: module.vis,
            mod_token: module.mod_token,
            ident: module.ident,
            brace,
            items,
        })
    }
}

impl quote::ToTokens for ItemMod {
    /// We mainly implement this trait for pro! module to have a derived
    /// [`Spanned`](`syn::spanned::Spanned`) implementation for it.
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        tokens.append_all(
            self.attrs
                .iter()
                .filter(|attr| matches!(attr.style, syn::AttrStyle::Outer)),
        );
        self.vis.to_tokens(tokens);
        self.mod_token.to_tokens(tokens);
        self.ident.to_tokens(tokens);
        self.brace.surround(tokens, |tokens| {
            tokens.append_all(
                self.attrs
                    .iter()
                    .filter(|attr| matches!(attr.style, syn::AttrStyle::Inner(_))),
            );
            tokens.append_all(&self.items);
        });
    }
}

impl ItemMod {
    /// Returns the identifier of the pro! module.
    pub fn ident(&self) -> &Ident {
        &self.ident
    }

    /// Returns the storage struct definition for this pro! module.
    ///
    /// # Note
    ///
    /// The storage definition is the struct that has been annotated with
    /// `#[pro(storage)]`. This struct is required to be defined in the root
    /// of the pro! inline module.
    ///
    /// # Panics
    ///
    /// If zero or multiple `#[pro(storage)]` annotated structs were found in
    /// the pro! module. This can be expected to never happen since upon
    /// construction of an pro! module it is asserted that exactly one
    /// `#[pro(storage)]` struct exists.
    pub fn storage(&self) -> &ir::Storage {
        let mut iter = IterProItems::new(self)
            .filter_map(|pro_item| pro_item.filter_map_storage_item());
        let storage = iter
            .next()
            .expect("encountered pro! module without a storage struct");
        assert!(
            iter.next().is_none(),
            "encountered multiple storage structs in pro! module"
        );
        storage
    }

    /// Returns all (pro! and non-pro! specific) item definitions of the pro! inline module.
    pub fn items(&self) -> &[ir::Item] {
        self.items.as_slice()
    }

    /// Returns an iterator yielding all pro! implementation blocks.
    ///
    /// # Note
    ///
    /// An pro! implementation block can be either an inherent `impl` block
    /// directly defined for the contract's storage struct if it includes at
    /// least one `#[pro(message)]` or `#[pro(constructor)]` annotation, e.g.:
    ///
    /// ```
    /// # use core::convert::TryFrom;
    /// # use pro_lang_ir as ir;
    /// # <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(syn::parse_quote! {
    /// # mod my_module {
    /// # #[pro(storage)]
    /// # pub struct MyStorage {
    /// #     /* storage fields */
    /// # }
    /// #
    /// impl MyStorage {
    /// #   #[pro(constructor)]
    /// #   pub fn my_constructor() -> Self {
    /// #       /* constructor implementation */
    /// #   }
    /// #
    ///     #[pro(message)]
    ///     pub fn my_message(&self) {
    ///         /* message implementation */
    ///     }
    /// }
    /// # }}).unwrap();
    /// ```
    ///
    /// Also an implementation block can be defined as a trait implementation
    /// for the pro! storage struct using the `#[pro(impl)]` annotation even
    /// if none of its interior items have any pro! specific attributes on them,
    /// e.g.:
    ///
    /// ```
    /// # use core::convert::TryFrom;
    /// # use pro_lang_ir as ir;
    /// # <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(syn::parse_quote! {
    /// # mod my_module {
    /// # #[pro(storage)]
    /// # pub struct MyStorage {
    /// #     /* storage fields */
    /// # }
    /// #
    /// #[pro(impl)]
    /// impl MyStorage {
    ///     fn my_method(&self) -> i32 {
    ///         /* method implementation */
    ///     }
    /// }
    /// #
    /// # impl MyStorage {
    /// #   #[pro(constructor)]
    /// #   pub fn my_constructor() -> Self {
    /// #       /* constructor implementation */
    /// #   }
    /// #
    /// #   #[pro(message)]
    /// #   pub fn my_message(&self) {
    /// #       /* message implementation */
    /// #   }
    /// # }
    /// # }}).unwrap();
    /// ```
    pub fn impls(&self) -> IterItemImpls {
        IterItemImpls::new(self)
    }

    /// Returns an iterator yielding all event definitions in this pro! module.
    pub fn events(&self) -> IterEvents {
        IterEvents::new(self)
    }

    /// Returns all non-pro! attributes of the pro! module.
    pub fn attrs(&self) -> &[syn::Attribute] {
        &self.attrs
    }

    /// Returns the visibility of the pro! module.
    pub fn vis(&self) -> &syn::Visibility {
        &self.vis
    }
}

/// Iterator yielding pro! item definitions of the pro! smart contract.
pub struct IterProItems<'a> {
    items_iter: core::slice::Iter<'a, ir::Item>,
}

impl<'a> IterProItems<'a> {
    /// Creates a new pro! module items iterator.
    fn new(pro_module: &'a ItemMod) -> Self {
        Self {
            items_iter: pro_module.items.iter(),
        }
    }
}

impl<'a> Iterator for IterProItems<'a> {
    type Item = &'a ir::ProItem;

    fn next(&mut self) -> Option<Self::Item> {
        'repeat: loop {
            match self.items_iter.next() {
                None => return None,
                Some(item) => {
                    if let Some(event) = item.map_pro_item() {
                        return Some(event)
                    }
                    continue 'repeat
                }
            }
        }
    }
}

/// Iterator yielding all pro! event definitions within the pro!
/// [`ItemMod`](`crate::ir::ItemMod`).
pub struct IterEvents<'a> {
    items_iter: IterProItems<'a>,
}

impl<'a> IterEvents<'a> {
    /// Creates a new pro! events iterator.
    fn new(pro_module: &'a ItemMod) -> Self {
        Self {
            items_iter: IterProItems::new(pro_module),
        }
    }
}

impl<'a> Iterator for IterEvents<'a> {
    type Item = &'a ir::Event;

    fn next(&mut self) -> Option<Self::Item> {
        'repeat: loop {
            match self.items_iter.next() {
                None => return None,
                Some(pro_item) => {
                    if let Some(event) = pro_item.filter_map_event_item() {
                        return Some(event)
                    }
                    continue 'repeat
                }
            }
        }
    }
}

/// Iterator yielding all pro! implementation block definitions within the pro!
/// [`ItemMod`](`crate::ir::ItemMod`).
pub struct IterItemImpls<'a> {
    items_iter: IterProItems<'a>,
}

impl<'a> IterItemImpls<'a> {
    /// Creates a new pro! implementation blocks iterator.
    fn new(pro_module: &'a ItemMod) -> Self {
        Self {
            items_iter: IterProItems::new(pro_module),
        }
    }
}

impl<'a> Iterator for IterItemImpls<'a> {
    type Item = &'a ir::ItemImpl;

    fn next(&mut self) -> Option<Self::Item> {
        'repeat: loop {
            match self.items_iter.next() {
                None => return None,
                Some(pro_item) => {
                    if let Some(event) = pro_item.filter_map_impl_block() {
                        return Some(event)
                    }
                    continue 'repeat
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate as ir;

    #[test]
    fn item_mod_try_from_works() {
        let item_mods: Vec<syn::ItemMod> = vec![
            syn::parse_quote! {
                mod minimal {
                    #[pro(storage)]
                    pub struct Minimal {}

                    impl Minimal {
                        #[pro(constructor)]
                        pub fn new() -> Self {}
                        #[pro(message)]
                        pub fn minimal_message(&self) {}
                    }
                }
            },
            syn::parse_quote! {
                mod flipper {
                    #[pro(storage)]
                    pub struct Flipper {
                        value: bool,
                    }

                    impl Default for Flipper {
                        #[pro(constructor)]
                        fn default() -> Self {
                            Self { value: false }
                        }
                    }

                    impl Flipper {
                        #[pro(message)]
                        pub fn flip(&mut self) {
                            self.value = !self.value
                        }

                        #[pro(message)]
                        pub fn get(&self) -> bool {
                            self.value
                        }
                    }
                }
            },
        ];
        for item_mod in item_mods {
            assert!(<ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(item_mod).is_ok())
        }
    }

    fn assert_fail(item_mod: syn::ItemMod, expected_err: &str) {
        assert_eq!(
            <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(item_mod)
                .map_err(|err| err.to_string()),
            Err(expected_err.to_string()),
        );
    }

    #[test]
    fn missing_storage_struct_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    impl MyStorage {
                        #[pro(constructor)]
                        pub fn my_constructor() -> Self {}
                        #[pro(message)]
                        pub fn my_message(&self) {}
                    }
                }
            },
            "missing pro! storage struct",
        )
    }

    #[test]
    fn multiple_storage_struct_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyFirstStorage {}
                    #[pro(storage)]
                    pub struct MySecondStorage {}
                    impl MyFirstStorage {
                        #[pro(constructor)]
                        pub fn my_constructor() -> Self {}
                        #[pro(message)]
                        pub fn my_message(&self) {}
                    }
                }
            },
            "encountered multiple pro! storage structs, expected exactly one",
        )
    }

    #[test]
    fn missing_constructor_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl MyStorage {
                        #[pro(message)]
                        pub fn my_message(&self) {}
                    }
                }
            },
            "missing pro! constructor",
        )
    }

    #[test]
    fn missing_message_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl MyStorage {
                        #[pro(constructor)]
                        pub fn my_constructor() -> Self {}
                    }
                }
            },
            "missing pro! message",
        )
    }

    #[test]
    fn invalid_out_of_line_module_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module;
            },
            "out-of-line pro! modules are not supported, use `#[pro::contract] mod name { ... }`",
        )
    }

    #[test]
    fn conflicting_attributes_fails() {
        assert_fail(
            syn::parse_quote! {
                #[pro(namespace = "my_namespace")]
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}
                    impl MyStorage {
                        #[pro(constructor)]
                        pub fn my_constructor() -> Self {}
                        #[pro(message)]
                        pub fn my_message(&self) {}
                    }
                }
            },
            "encountered invalid pro! attributes on pro! module",
        )
    }

    #[test]
    fn overlapping_messages_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl MyStorage {
                        #[pro(constructor)]
                        pub fn my_constructor() -> Self {}

                        #[pro(message, selector = "0xDEADBEEF")]
                        pub fn my_message_1(&self) {}
                    }

                    impl MyStorage {
                        #[pro(message, selector = "0xDEADBEEF")]
                        pub fn my_message_2(&self) {}
                    }
                }
            },
            "encountered pro! messages with overlapping selectors (= [DE, AD, BE, EF])\n\
                hint: use #[pro(selector = \"0x...\")] on the callable or \
                #[pro(namespace = \"...\")] on the implementation block to \
                disambiguate overlapping selectors.",
        );
    }

    #[test]
    fn overlapping_constructors_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl MyStorage {
                        #[pro(constructor, selector = "0xDEADBEEF")]
                        pub fn my_constructor_1() -> Self {}

                        #[pro(message)]
                        pub fn my_message_1(&self) {}
                    }

                    impl MyStorage {
                        #[pro(constructor, selector = "0xDEADBEEF")]
                        pub fn my_constructor_2() -> Self {}
                    }
                }
            },
            "encountered pro! constructors with overlapping selectors (= [DE, AD, BE, EF])\n\
                hint: use #[pro(selector = \"0x...\")] on the callable or \
                #[pro(namespace = \"...\")] on the implementation block to \
                disambiguate overlapping selectors.",
        );
    }

    #[test]
    fn overlapping_trait_impls_fails() {
        assert_fail(
            syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl first::MyTrait for MyStorage {
                        #[pro(constructor)]
                        fn my_constructor() -> Self {}

                        #[pro(message)]
                        fn my_message(&self) {}
                    }

                    impl second::MyTrait for MyStorage {
                        #[pro(message)]
                        fn my_message(&self) {}
                    }
                }
            },
            "encountered pro! messages with overlapping selectors (= [EA, 48, 09, 33])\n\
                hint: use #[pro(selector = \"0x...\")] on the callable or \
                #[pro(namespace = \"...\")] on the implementation block to \
                disambiguate overlapping selectors.",
        );
    }

    #[test]
    fn namespaced_overlapping_trait_impls_works() {
        assert!(
            <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    #[pro(namespace = "first")]
                    impl first::MyTrait for MyStorage {
                        #[pro(constructor)]
                        fn my_constructor() -> Self {}

                        #[pro(message)]
                        fn my_message(&self) {}
                    }

                    impl second::MyTrait for MyStorage {
                        #[pro(message)]
                        fn my_message(&self) {}
                    }
                }
            })
            .is_ok()
        );
    }

    #[test]
    fn allow_overlap_between_messages_and_constructors() {
        assert!(
            <ir::ItemMod as TryFrom<syn::ItemMod>>::try_from(syn::parse_quote! {
                mod my_module {
                    #[pro(storage)]
                    pub struct MyStorage {}

                    impl MyStorage {
                        #[pro(constructor, selector = "0xDEADBEEF")]
                        pub fn my_constructor() -> Self {}

                        #[pro(message, selector = "0xDEADBEEF")]
                        pub fn my_message(&self) {}
                    }
                }
            })
            .is_ok()
        );
    }
}
