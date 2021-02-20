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
    TokenStream as TokenStream2,
};
use syn::{
    spanned::Spanned as _,
    Result,
};

/// A checked pro! trait definition.
#[derive(Debug, PartialEq, Eq)]
pub struct ProTrait {
    item: syn::ItemTrait,
}

impl TryFrom<syn::ItemTrait> for ProTrait {
    type Error = syn::Error;

    fn try_from(item_trait: syn::ItemTrait) -> core::result::Result<Self, Self::Error> {
        idents_lint::ensure_no_pro_identifiers(&item_trait)?;
        Self::analyse_properties(&item_trait)?;
        Self::analyse_items(&item_trait)?;
        Ok(Self { item: item_trait })
    }
}

impl ProTrait {
    /// Returns the hash to verify that the trait definition has been checked.
    pub fn compute_verify_hash<C, M>(
        trait_name: &Ident,
        constructors: C,
        messages: M,
    ) -> [u8; 32]
    where
        // Name and number of inputs.
        C: Iterator<Item = (Ident, usize)>,
        // Name, number of inputs and true if message may mutate storage.
        M: Iterator<Item = (Ident, usize, bool)>,
    {
        let mut constructors = constructors
            .map(|(name, len_inputs)| {
                [name.to_string(), len_inputs.to_string()].join(":")
            })
            .collect::<Vec<_>>();
        let mut messages = messages
            .map(|(name, len_inputs, mutability)| {
                let mutability = match mutability {
                    true => "w",
                    false => "r",
                };
                [
                    name.to_string(),
                    len_inputs.to_string(),
                    mutability.to_string(),
                ]
                .join(":")
            })
            .collect::<Vec<_>>();
        constructors.sort_unstable();
        messages.sort_unstable();
        let joined_constructors = constructors.join(",");
        let joined_messages = messages.join(",");
        let mut buffer = vec!["__pro_trait".to_string(), trait_name.to_string()];
        if !joined_constructors.is_empty() {
            buffer.push(joined_constructors);
        }
        if !joined_messages.is_empty() {
            buffer.push(joined_messages);
        }
        let buffer = buffer.join("::").into_bytes();
        use blake2::digest::generic_array::sequence::Split as _;
        let (head_32, _rest) =
            <blake2::Blake2b as blake2::Digest>::digest(&buffer).split();
        head_32.into()
    }

    /// Returns the hash to verify that the trait definition has been checked.
    pub fn verify_hash(&self) -> [u8; 32] {
        let trait_name = self.ident();
        Self::compute_verify_hash(
            trait_name,
            self.iter_items()
                .flat_map(ProTraitItem::filter_map_constructor)
                .map(|constructor| {
                    let name = constructor.sig().ident.clone();
                    let len_inputs = constructor.sig().inputs.len();
                    (name, len_inputs)
                }),
            self.iter_items()
                .flat_map(ProTraitItem::filter_map_message)
                .map(|message| {
                    let name = message.sig().ident.clone();
                    let len_inputs = message.sig().inputs.len();
                    let mutability = message.mutates();
                    (name, len_inputs, mutability)
                }),
        )
    }
}

/// Iterator over all the pro! trait items of an pro! trait definition.
pub struct IterProTraitItems<'a> {
    iter: core::slice::Iter<'a, syn::TraitItem>,
}

impl<'a> IterProTraitItems<'a> {
    /// Creates a new iterator yielding pro! trait items.
    fn new(item_trait: &'a ProTrait) -> Self {
        Self {
            iter: item_trait.item.items.iter(),
        }
    }
}

impl<'a> Iterator for IterProTraitItems<'a> {
    type Item = ProTraitItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            match self.iter.next() {
                None => return None,
                Some(syn::TraitItem::Method(method)) => {
                    let first_attr = ir::first_pro_attribute(&method.attrs)
                        .ok()
                        .flatten()
                        .expect("unexpected missing pro! attribute for trait method")
                        .first()
                        .kind()
                        .clone();
                    match first_attr {
                        ir::AttributeArg::Constructor => {
                            return Some(ProTraitItem::Constructor(ProTraitConstructor {
                                item: method,
                            }))
                        }
                        ir::AttributeArg::Message => {
                            return Some(ProTraitItem::Message(ProTraitMessage {
                                item: method,
                            }))
                        }
                        _ => continue 'outer,
                    }
                }
                Some(_) => continue 'outer,
            }
        }
    }
}

/// An pro! item within an pro! trait definition.
#[derive(Debug, Clone)]
pub enum ProTraitItem<'a> {
    Constructor(ProTraitConstructor<'a>),
    Message(ProTraitMessage<'a>),
}

impl<'a> ProTraitItem<'a> {
    /// Returns `Some` if the pro! trait item is a constructor.
    pub fn filter_map_constructor(self) -> Option<ProTraitConstructor<'a>> {
        match self {
            Self::Constructor(pro_trait_constructor) => Some(pro_trait_constructor),
            _ => None,
        }
    }

    /// Returns `Some` if the pro! trait item is a message.
    pub fn filter_map_message(self) -> Option<ProTraitMessage<'a>> {
        match self {
            Self::Message(pro_trait_message) => Some(pro_trait_message),
            _ => None,
        }
    }
}

/// Returns all non-pro! attributes.
///
/// # Panics
///
/// If there are malformed pro! attributes in the input.
fn extract_rust_attributes(attributes: &[syn::Attribute]) -> Vec<syn::Attribute> {
    let (_pro_attrs, rust_attrs) = ir::partition_attributes(attributes.to_vec())
        .expect("encountered unexpected invalid pro! attributes");
    rust_attrs
}

/// A checked pro! constructor of an pro! trait definition.
#[derive(Debug, Clone)]
pub struct ProTraitConstructor<'a> {
    item: &'a syn::TraitItemMethod,
}

impl<'a> ProTraitConstructor<'a> {
    /// Returns all non-pro! attributes.
    pub fn attrs(&self) -> Vec<syn::Attribute> {
        extract_rust_attributes(&self.item.attrs)
    }

    /// Returns the original signature of the pro! constructor.
    pub fn sig(&self) -> &syn::Signature {
        &self.item.sig
    }

    /// Returns the span of the pro! constructor.
    pub fn span(&self) -> Span {
        self.item.span()
    }
}

/// A checked pro! message of an pro! trait definition.
#[derive(Debug, Clone)]
pub struct ProTraitMessage<'a> {
    item: &'a syn::TraitItemMethod,
}

impl<'a> ProTraitMessage<'a> {
    /// Returns all non-pro! attributes.
    pub fn attrs(&self) -> Vec<syn::Attribute> {
        extract_rust_attributes(&self.item.attrs)
    }

    /// Returns the original signature of the pro! message.
    pub fn sig(&self) -> &syn::Signature {
        &self.item.sig
    }

    /// Returns the span of the pro! message.
    pub fn span(&self) -> Span {
        self.item.span()
    }

    /// Returns `true` if the pro! message may mutate the contract storage.
    pub fn mutates(&self) -> bool {
        self.sig()
            .receiver()
            .map(|fn_arg| {
                match fn_arg {
                    syn::FnArg::Receiver(receiver) if receiver.mutability.is_some() => {
                        true
                    }
                    syn::FnArg::Typed(pat_type) => {
                        match &*pat_type.ty {
                            syn::Type::Reference(reference)
                                if reference.mutability.is_some() =>
                            {
                                true
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                }
            })
            .expect("encountered missing receiver for pro! message")
    }
}

impl ProTrait {
    /// Returns `Ok` if the trait matches all requirements for an pro! trait definition.
    pub fn new(attr: TokenStream2, input: TokenStream2) -> Result<Self> {
        if !attr.is_empty() {
            return Err(format_err_spanned!(
                attr,
                "unexpected attribute input for pro! trait definition"
            ))
        }
        let item_trait = syn::parse2::<syn::ItemTrait>(input)?;
        ProTrait::try_from(item_trait)
    }

    /// Returns span of the pro! trait definition.
    pub fn span(&self) -> Span {
        self.item.span()
    }

    /// Returns the attributes of the pro! trait definition.
    pub fn attrs(&self) -> &[syn::Attribute] {
        &self.item.attrs
    }

    /// Returns the identifier of the pro! trait definition.
    pub fn ident(&self) -> &Ident {
        &self.item.ident
    }

    /// Returns an iterator yielding the pro! specific items of the pro! trait definition.
    pub fn iter_items(&self) -> IterProTraitItems {
        IterProTraitItems::new(self)
    }

    /// Analyses the properties of the pro! trait definition.
    ///
    /// # Errors
    ///
    /// - If the trait has been defined as `unsafe`.
    /// - If the trait is an automatically implemented trait (`auto trait`).
    /// - If the trait is generic over some set of types.
    /// - If the trait's visibility is not public (`pub`).
    fn analyse_properties(item_trait: &syn::ItemTrait) -> Result<()> {
        if let Some(unsafety) = &item_trait.unsafety {
            return Err(format_err_spanned!(
                unsafety,
                "pro! trait definitions cannot be unsafe"
            ))
        }
        if let Some(auto) = &item_trait.auto_token {
            return Err(format_err_spanned!(
                auto,
                "pro! trait definitions cannot be automatically implemented traits"
            ))
        }
        if !item_trait.generics.params.is_empty() {
            return Err(format_err_spanned!(
                item_trait.generics.params,
                "pro! trait definitions must not be generic"
            ))
        }
        if !matches!(item_trait.vis, syn::Visibility::Public(_)) {
            return Err(format_err_spanned!(
                item_trait.vis,
                "pro! trait definitions must have public visibility"
            ))
        }
        if !item_trait.supertraits.is_empty() {
            return Err(format_err_spanned!(
                item_trait.supertraits,
                "pro! trait definitions with supertraits are not supported, yet"
            ))
        }
        Ok(())
    }

    /// Returns `Ok` if all trait items respects the requirements for an pro! trait definition.
    ///
    /// # Errors
    ///
    /// - If the trait contains an unsupported trait item such as
    ///     - associated constants (`const`)
    ///     - associated types (`type`)
    ///     - macros definitions or usages
    ///     - unknown token sequences (verbatims)
    ///     - methods with default implementations
    /// - If the trait contains methods which do not respect the pro! trait definition requirements:
    ///     - All trait methods need to be declared as either `#[pro(message)]` or `#[pro(constructor)]`
    ///       and need to respect their respective rules.
    ///
    /// # Note
    ///
    /// Associated types and constants might be allowed in the future.
    fn analyse_items(item_trait: &syn::ItemTrait) -> Result<()> {
        for trait_item in &item_trait.items {
            match trait_item {
                syn::TraitItem::Const(const_trait_item) => {
                    return Err(format_err_spanned!(
                        const_trait_item,
                        "associated constants in pro! trait definitions are not supported, yet"
                    ))
                }
                syn::TraitItem::Macro(macro_trait_item) => {
                    return Err(format_err_spanned!(
                        macro_trait_item,
                        "macros in pro! trait definitions are not supported"
                    ))
                }
                syn::TraitItem::Type(type_trait_item) => {
                    return Err(format_err_spanned!(
                    type_trait_item,
                    "associated types in pro! trait definitions are not supported, yet"
                ))
                }
                syn::TraitItem::Verbatim(verbatim) => {
                    return Err(format_err_spanned!(
                        verbatim,
                        "encountered unsupported item in pro! trait definition"
                    ))
                }
                syn::TraitItem::Method(method_trait_item) => {
                    Self::analyse_methods(method_trait_item)?;
                }
                unknown => {
                    return Err(format_err_spanned!(
                        unknown,
                        "encountered unknown or unsupported item in pro! trait definition"
                    ))
                }
            }
        }
        Ok(())
    }

    /// Analyses an pro! method that can be either an pro! message or constructor.
    ///
    /// # Errors
    ///
    /// - If the method declared as `unsafe`, `const` or `async`.
    /// - If the method has some explicit API.
    /// - If the method is variadic or has generic parameters.
    /// - If the method does not respect the properties of either an
    ///   pro! message or pro! constructor.
    fn analyse_methods(method: &syn::TraitItemMethod) -> Result<()> {
        if let Some(default_impl) = &method.default {
            return Err(format_err_spanned!(
                default_impl,
                "pro! trait methods with default implementations are not supported"
            ))
        }
        if let Some(constness) = &method.sig.constness {
            return Err(format_err_spanned!(
                constness,
                "const pro! trait methods are not supported"
            ))
        }
        if let Some(asyncness) = &method.sig.asyncness {
            return Err(format_err_spanned!(
                asyncness,
                "async pro! trait methods are not supported"
            ))
        }
        if let Some(unsafety) = &method.sig.unsafety {
            return Err(format_err_spanned!(
                unsafety,
                "unsafe pro! trait methods are not supported"
            ))
        }
        if let Some(abi) = &method.sig.abi {
            return Err(format_err_spanned!(
                abi,
                "pro! trait methods with non default ABI are not supported"
            ))
        }
        if let Some(variadic) = &method.sig.variadic {
            return Err(format_err_spanned!(
                variadic,
                "variadic pro! trait methods are not supported"
            ))
        }
        if !method.sig.generics.params.is_empty() {
            return Err(format_err_spanned!(
                method.sig.generics.params,
                "generic pro! trait methods are not supported"
            ))
        }
        match ir::first_pro_attribute(&method.attrs) {
            Ok(Some(pro_attr)) => {
                match pro_attr.first().kind() {
                    ir::AttributeArg::Message => {
                        Self::analyse_message(method)?;
                    }
                    ir::AttributeArg::Constructor => {
                        Self::analyse_constructor(method)?;
                    }
                    _unsupported => {
                        return Err(format_err_spanned!(
                            method,
                            "encountered unsupported pro! attribute for pro! trait method",
                        ))
                    }
                }
            }
            Ok(None) => {
                return Err(format_err_spanned!(
                    method,
                    "missing #[pro(message)] or #[pro(constructor)] flags on pro! trait method"
                ))
            }
            Err(err) => return Err(err),
        }
        Ok(())
    }

    /// Analyses the properties of an pro! constructor.
    ///
    /// # Errors
    ///
    /// - If the constructor has a `self` receiver as first argument.
    /// - If the constructor has no `Self` return type.
    fn analyse_constructor(constructor: &syn::TraitItemMethod) -> Result<()> {
        ir::sanitize_attributes(
            constructor.span(),
            constructor.attrs.clone(),
            &ir::AttributeArgKind::Constructor,
            |arg| {
                match arg.kind() {
                    ir::AttributeArg::Constructor => Ok(()),
                    _ => Err(None),
                }
            },
        )?;
        if let Some(receiver) = constructor.sig.receiver() {
            return Err(format_err_spanned!(
                receiver,
                "pro! constructors must not have a `self` receiver",
            ))
        }
        match &constructor.sig.output {
            syn::ReturnType::Default => {
                return Err(format_err_spanned!(
                    constructor.sig,
                    "pro! constructors must return Self"
                ))
            }
            syn::ReturnType::Type(_, ty) => {
                match &**ty {
                    syn::Type::Path(type_path) => {
                        if !type_path.path.is_ident("Self") {
                            return Err(format_err_spanned!(
                                type_path.path,
                                "pro! constructors must return Self"
                            ))
                        }
                    }
                    unknown => {
                        return Err(format_err_spanned!(
                            unknown,
                            "pro! constructors must return Self"
                        ))
                    }
                }
            }
        }
        Ok(())
    }

    /// Analyses the properties of an pro! message.
    ///
    /// # Errors
    ///
    /// - If the message has no `&self` or `&mut self` receiver.
    fn analyse_message(message: &syn::TraitItemMethod) -> Result<()> {
        ir::sanitize_attributes(
            message.span(),
            message.attrs.clone(),
            &ir::AttributeArgKind::Message,
            |arg| {
                match arg.kind() {
                    ir::AttributeArg::Message => Ok(()),
                    _ => Err(None),
                }
            },
        )?;
        match message.sig.receiver() {
            None | Some(syn::FnArg::Typed(_)) => {
                return Err(format_err_spanned!(
                message.sig,
                "missing or malformed `&self` or `&mut self` receiver for pro! message",
            ))
            }
            Some(syn::FnArg::Receiver(receiver)) => {
                if receiver.reference.is_none() {
                    return Err(format_err_spanned!(
                        receiver,
                        "self receiver of pro! message must be `&self` or `&mut self`"
                    ))
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks if the token stream in `$trait_def` results in the expected error message.
    macro_rules! assert_pro_trait_eq_err {
        ( error: $err_str:literal, $($trait_def:tt)* ) => {
            assert_eq!(
                <ProTrait as TryFrom<syn::ItemTrait>>::try_from(syn::parse_quote! {
                    $( $trait_def )*
                })
                .map_err(|err| err.to_string()),
                Err(
                    $err_str.to_string()
                )
            )
        };
    }

    #[test]
    fn unsafe_trait_def_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions cannot be unsafe",
            pub unsafe trait MyTrait {}
        );
    }

    #[test]
    fn auto_trait_def_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions cannot be automatically implemented traits",
            pub auto trait MyTrait {}
        );
    }

    #[test]
    fn non_pub_trait_def_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions must have public visibility",
            trait MyTrait {}
        );
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions must have public visibility",
            pub(crate) trait MyTrait {}
        );
    }

    #[test]
    fn generic_trait_def_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions must not be generic",
            pub trait MyTrait<T> {}
        );
    }

    #[test]
    fn trait_def_with_supertraits_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait definitions with supertraits are not supported, yet",
            pub trait MyTrait: SuperTrait {}
        );
    }

    #[test]
    fn trait_def_containing_const_item_is_denied() {
        assert_pro_trait_eq_err!(
            error: "associated constants in pro! trait definitions are not supported, yet",
            pub trait MyTrait {
                const T: i32;
            }
        );
    }

    #[test]
    fn trait_def_containing_associated_type_is_denied() {
        assert_pro_trait_eq_err!(
            error: "associated types in pro! trait definitions are not supported, yet",
            pub trait MyTrait {
                type Type;
            }
        );
    }

    #[test]
    fn trait_def_containing_macro_is_denied() {
        assert_pro_trait_eq_err!(
            error: "macros in pro! trait definitions are not supported",
            pub trait MyTrait {
                my_macro_call!();
            }
        );
    }

    #[test]
    fn trait_def_containing_non_flagged_method_is_denied() {
        assert_pro_trait_eq_err!(
            error: "missing #[pro(message)] or #[pro(constructor)] flags on pro! trait method",
            pub trait MyTrait {
                fn non_flagged_1(&self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "missing #[pro(message)] or #[pro(constructor)] flags on pro! trait method",
            pub trait MyTrait {
                fn non_flagged_2(&mut self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "missing #[pro(message)] or #[pro(constructor)] flags on pro! trait method",
            pub trait MyTrait {
                fn non_flagged_3() -> Self;
            }
        );
    }

    #[test]
    fn trait_def_containing_default_implemented_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait methods with default implementations are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                fn default_implemented() -> Self {}
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! trait methods with default implementations are not supported",
            pub trait MyTrait {
                #[pro(message)]
                fn default_implemented(&self) {}
            }
        );
    }

    #[test]
    fn trait_def_containing_const_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "const pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                const fn const_constructor() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "const pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(message)]
                const fn const_message(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_async_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "async pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                async fn const_constructor() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "async pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(message)]
                async fn const_message(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_unsafe_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "unsafe pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                unsafe fn const_constructor() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "unsafe pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(message)]
                unsafe fn const_message(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_methods_using_explicit_abi_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! trait methods with non default ABI are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                extern fn const_constructor() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! trait methods with non default ABI are not supported",
            pub trait MyTrait {
                #[pro(message)]
                extern fn const_message(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_variadic_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "variadic pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                fn const_constructor(...) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "variadic pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(message)]
                fn const_message(&self, ...);
            }
        );
    }

    #[test]
    fn trait_def_containing_generic_methods_is_denied() {
        assert_pro_trait_eq_err!(
            error: "generic pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(constructor)]
                fn const_constructor<T>() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "generic pro! trait methods are not supported",
            pub trait MyTrait {
                #[pro(message)]
                fn const_message<T>(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_method_with_unsupported_pro_attribute_is_denied() {
        assert_pro_trait_eq_err!(
            error: "encountered unsupported pro! attribute for pro! trait method",
            pub trait MyTrait {
                #[pro(payable)]
                fn unsupported_pro_attribute(&self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "unknown pro! attribute (path)",
            pub trait MyTrait {
                #[pro(unknown)]
                fn unknown_pro_attribute(&self);
            }
        );
    }

    #[test]
    fn trait_def_containing_invalid_constructor_is_denied() {
        assert_pro_trait_eq_err!(
            error: "pro! constructors must not have a `self` receiver",
            pub trait MyTrait {
                #[pro(constructor)]
                fn has_self_receiver(&self) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must not have a `self` receiver",
            pub trait MyTrait {
                #[pro(constructor)]
                fn has_self_receiver(&mut self) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must not have a `self` receiver",
            pub trait MyTrait {
                #[pro(constructor)]
                fn has_self_receiver(self) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must not have a `self` receiver",
            pub trait MyTrait {
                #[pro(constructor)]
                fn has_self_receiver(self: &Self) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must not have a `self` receiver",
            pub trait MyTrait {
                #[pro(constructor)]
                fn has_self_receiver(self: Self) -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must return Self",
            pub trait MyTrait {
                #[pro(constructor)]
                fn does_not_return_self();
            }
        );
        assert_pro_trait_eq_err!(
            error: "pro! constructors must return Self",
            pub trait MyTrait {
                #[pro(constructor)]
                fn does_not_return_self() -> i32;
            }
        );
    }

    #[test]
    fn trait_def_containing_invalid_message_is_denied() {
        assert_pro_trait_eq_err!(
            error: "missing or malformed `&self` or `&mut self` receiver for pro! message",
            pub trait MyTrait {
                #[pro(message)]
                fn does_not_return_self();
            }
        );
        assert_pro_trait_eq_err!(
            error: "missing or malformed `&self` or `&mut self` receiver for pro! message",
            pub trait MyTrait {
                #[pro(message)]
                fn does_not_return_self(self: &Self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "self receiver of pro! message must be `&self` or `&mut self`",
            pub trait MyTrait {
                #[pro(message)]
                fn does_not_return_self(self);
            }
        );
    }

    #[test]
    fn trait_def_containing_constructor_with_invalid_pro_attributes_is_denied() {
        assert_pro_trait_eq_err!(
            error: "encountered duplicate pro! attribute",
            pub trait MyTrait {
                #[pro(constructor)]
                #[pro(constructor)]
                fn does_not_return_self() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "encountered conflicting pro! attribute argument",
            pub trait MyTrait {
                #[pro(constructor)]
                #[pro(message)]
                fn does_not_return_self() -> Self;
            }
        );
        assert_pro_trait_eq_err!(
            error: "encountered conflicting pro! attribute argument",
            pub trait MyTrait {
                #[pro(constructor)]
                #[pro(payable)]
                fn does_not_return_self() -> Self;
            }
        );
    }

    #[test]
    fn trait_def_containing_message_with_invalid_pro_attributes_is_denied() {
        assert_pro_trait_eq_err!(
            error: "encountered duplicate pro! attribute",
            pub trait MyTrait {
                #[pro(message)]
                #[pro(message)]
                fn does_not_return_self(&self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "encountered conflicting pro! attribute argument",
            pub trait MyTrait {
                #[pro(message)]
                #[pro(constructor)]
                fn does_not_return_self(&self);
            }
        );
        assert_pro_trait_eq_err!(
            error: "encountered conflicting pro! attribute argument",
            pub trait MyTrait {
                #[pro(message)]
                #[pro(payable)]
                fn does_not_return_self(&self);
            }
        );
    }

    #[test]
    fn trait_def_is_ok() {
        assert!(
            <ProTrait as TryFrom<syn::ItemTrait>>::try_from(syn::parse_quote! {
                pub trait MyTrait {
                    #[pro(constructor)]
                    fn my_constructor() -> Self;
                    #[pro(message)]
                    fn my_message(&self);
                    #[pro(message)]
                    fn my_message_mut(&mut self);
                }
            })
            .is_ok()
        )
    }

    #[test]
    fn iter_constructors_works() {
        let pro_trait =
            <ProTrait as TryFrom<syn::ItemTrait>>::try_from(syn::parse_quote! {
                pub trait MyTrait {
                    #[pro(constructor)]
                    fn constructor_1() -> Self;
                    #[pro(constructor)]
                    fn constructor_2() -> Self;
                    #[pro(message)]
                    fn message_1(&self);
                    #[pro(message)]
                    fn message_2(&mut self);
                 }
            })
            .unwrap();
        let actual = pro_trait
            .iter_items()
            .flat_map(|item| {
                item.filter_map_constructor()
                    .map(|constructor| constructor.sig().ident.to_string())
            })
            .collect::<Vec<_>>();
        let expected = vec!["constructor_1".to_string(), "constructor_2".to_string()];
        assert_eq!(actual, expected);
    }

    #[test]
    fn iter_messages_works() {
        let pro_trait =
            <ProTrait as TryFrom<syn::ItemTrait>>::try_from(syn::parse_quote! {
                pub trait MyTrait {
                    #[pro(constructor)]
                    fn constructor_1() -> Self;
                    #[pro(constructor)]
                    fn constructor_2() -> Self;
                    #[pro(message)]
                    fn message_1(&self);
                    #[pro(message)]
                    fn message_2(&mut self);
                }
            })
            .unwrap();
        let actual = pro_trait
            .iter_items()
            .flat_map(|item| {
                item.filter_map_message()
                    .map(|message| message.sig().ident.to_string())
            })
            .collect::<Vec<_>>();
        let expected = vec!["message_1".to_string(), "message_2".to_string()];
        assert_eq!(actual, expected);
    }

    fn assert_verify_hash2_works_with(pro_trait: ProTrait, expected: &str) {
        let expected = expected.to_string().into_bytes();
        let actual = pro_trait.verify_hash();
        let expected: [u8; 32] = {
            use blake2::digest::generic_array::sequence::Split as _;
            let (head_32, _rest) =
                <blake2::Blake2b as blake2::Digest>::digest(&expected).split();
            head_32.into()
        };
        assert_eq!(actual, expected);
    }

    macro_rules! pro_trait {
        ( $($tt:tt)* ) => {{
            <ProTrait as TryFrom<syn::ItemTrait>>::try_from(syn::parse_quote! {
                $( $tt )*
            })
            .unwrap()
        }};
    }

    #[test]
    fn verify_hash_works() {
        let pro_trait = pro_trait! {
            pub trait MyTrait {
                #[pro(constructor)]
                fn constructor_1() -> Self;
                #[pro(constructor)]
                fn constructor_2(a: i32, b: i32) -> Self;
                #[pro(message)]
                fn message_1(&self);
                #[pro(message)]
                fn message_2(&mut self, a: i32, b: i32) -> i32;
            }
        };
        assert_verify_hash2_works_with(
            pro_trait,
            "__pro_trait::MyTrait::constructor_1:0,constructor_2:2::message_1:1:r,message_2:3:w"
        );
    }

    #[test]
    fn verify_hash_works_without_constructors() {
        let pro_trait = pro_trait! {
            pub trait MyTrait {
                #[pro(message)]
                fn message_1(&self);
                #[pro(message)]
                fn message_2(&mut self, a: i32, b: i32) -> i32;
            }
        };
        assert_verify_hash2_works_with(
            pro_trait,
            "__pro_trait::MyTrait::message_1:1:r,message_2:3:w",
        );
    }

    #[test]
    fn verify_hash_works_without_messages() {
        let pro_trait = pro_trait! {
            pub trait MyTrait {
                #[pro(constructor)]
                fn constructor_1() -> Self;
                #[pro(constructor)]
                fn constructor_2(a: i32, b: i32) -> Self;
            }
        };
        assert_verify_hash2_works_with(
            pro_trait,
            "__pro_trait::MyTrait::constructor_1:0,constructor_2:2",
        );
    }
}
