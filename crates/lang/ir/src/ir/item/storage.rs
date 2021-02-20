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
    ir::utils,
};
use core::convert::TryFrom;
use proc_macro2::Ident;
use syn::spanned::Spanned as _;

/// An pro! storage struct definition.
///
/// Noticed by pro! through the `#[pro(storage)]` annotation.
///
/// # Note
///
/// An pro! smart contract must have exactly one storage definition.
/// The storage definition must be found in the root of the pro! module.
///
/// # Example
///
/// ```
/// # use core::convert::TryFrom;
/// # <pro_lang_ir::Storage as TryFrom<syn::ItemStruct>>::try_from(syn::parse_quote! {
/// #[pro(storage)]
/// pub struct MyStorage {
///     my_value: bool,
///      counter: u32,
/// }
/// # }).unwrap();
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct Storage {
    /// The underlying `struct` Rust item.
    ast: syn::ItemStruct,
}

impl quote::ToTokens for Storage {
    /// We mainly implement this trait for this pro! type to have a derived
    /// [`Spanned`](`syn::spanned::Spanned`) implementation for it.
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.ast.to_tokens(tokens)
    }
}

impl Storage {
    /// Returns `true` if the first pro! annotation on the given struct is
    /// `#[pro(storage)]`.
    ///
    /// # Errors
    ///
    /// If the first found pro! attribute is malformed.
    pub(super) fn is_pro_storage(
        item_struct: &syn::ItemStruct,
    ) -> Result<bool, syn::Error> {
        if !ir::contains_pro_attributes(&item_struct.attrs) {
            return Ok(false)
        }
        // At this point we know that there must be at least one pro!
        // attribute. This can be either the pro! storage struct,
        // an pro! event or an invalid pro! attribute.
        let attr = ir::first_pro_attribute(&item_struct.attrs)?
            .expect("missing expected pro! attribute for struct");
        Ok(matches!(attr.first().kind(), ir::AttributeArg::Storage))
    }
}

impl TryFrom<syn::ItemStruct> for Storage {
    type Error = syn::Error;

    fn try_from(item_struct: syn::ItemStruct) -> Result<Self, Self::Error> {
        let struct_span = item_struct.span();
        let (_pro_attrs, other_attrs) = ir::sanitize_attributes(
            struct_span,
            item_struct.attrs,
            &ir::AttributeArgKind::Storage,
            |arg| {
                match arg.kind() {
                    ir::AttributeArg::Storage => Ok(()),
                    _ => Err(None),
                }
            },
        )?;
        if !item_struct.generics.params.is_empty() {
            return Err(format_err_spanned!(
                item_struct.generics.params,
                "generic pro! storage structs are not supported",
            ))
        }
        utils::ensure_pub_visibility("storage structs", struct_span, &item_struct.vis)?;
        Ok(Self {
            ast: syn::ItemStruct {
                attrs: other_attrs,
                ..item_struct
            },
        })
    }
}

impl Storage {
    /// Returns the non-pro! attributes of the pro! storage struct.
    pub fn attrs(&self) -> &[syn::Attribute] {
        &self.ast.attrs
    }

    /// Returns the identifier of the storage struct.
    pub fn ident(&self) -> &Ident {
        &self.ast.ident
    }

    /// Returns an iter yielding all fields of the storage struct.
    pub fn fields(&self) -> syn::punctuated::Iter<syn::Field> {
        self.ast.fields.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_try_from_works() {
        let item_struct: syn::ItemStruct = syn::parse_quote! {
            #[pro(storage)]
            pub struct MyStorage {
                field_1: i32,
                field_2: bool,
            }
        };
        assert!(Storage::try_from(item_struct).is_ok())
    }

    fn assert_try_from_fails(item_struct: syn::ItemStruct, expected: &str) {
        assert_eq!(
            Storage::try_from(item_struct).map_err(|err| err.to_string()),
            Err(expected.to_string())
        )
    }

    #[test]
    fn conflicting_attributes_fails() {
        assert_try_from_fails(
            syn::parse_quote! {
                #[pro(storage)]
                #[pro(event)]
                pub struct MyStorage {
                    field_1: i32,
                    field_2: bool,
                }
            },
            "encountered conflicting pro! attribute argument",
        )
    }

    #[test]
    fn duplicate_attributes_fails() {
        assert_try_from_fails(
            syn::parse_quote! {
                #[pro(storage)]
                #[pro(storage)]
                pub struct MyStorage {
                    field_1: i32,
                    field_2: bool,
                }
            },
            "encountered duplicate pro! attribute",
        )
    }

    #[test]
    fn wrong_first_attribute_fails() {
        assert_try_from_fails(
            syn::parse_quote! {
                #[pro(event)]
                #[pro(storage)]
                pub struct MyStorage {
                    field_1: i32,
                    field_2: bool,
                }
            },
            "unexpected first pro! attribute argument",
        )
    }

    #[test]
    fn missing_storage_attribute_fails() {
        assert_try_from_fails(
            syn::parse_quote! {
                pub struct MyStorage {
                    field_1: i32,
                    field_2: bool,
                }
            },
            "encountered unexpected empty expanded pro! attribute arguments",
        )
    }

    #[test]
    fn generic_storage_fails() {
        assert_try_from_fails(
            syn::parse_quote! {
                #[pro(storage)]
                pub struct GenericStorage<T> {
                    field_1: T,
                }
            },
            "generic pro! storage structs are not supported",
        )
    }

    #[test]
    fn non_pub_storage_struct() {
        assert_try_from_fails(
            syn::parse_quote! {
                #[pro(storage)]
                struct PrivateStorage {
                    field_1: i32,
                    field_2: bool,
                }
            },
            "non `pub` pro! storage structs are not supported",
        )
    }
}
