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

use super::{
    Constructor,
    Message,
};
use crate::{
    error::ExtError as _,
    ir,
    ir::attrs::Attrs as _,
};
use core::convert::TryFrom;
use syn::spanned::Spanned as _;

/// An item within an pro! implementation block.
///
/// Can be either
/// - an pro! [`ir::Constructor`](`crate::ir::Constructor`)
/// - an pro! [`ir::Message`](`crate::ir::Message`)
/// - or any other non-pro! item.
///
/// # Note
///
/// Based on [`syn::ImplItem`] with special variants for pro! impl items.
#[derive(Debug, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub enum ImplItem {
    /// A `#[pro(constructor)]` marked inherent function.
    Constructor(Constructor),
    /// A `#[pro(message)]` marked method.
    Message(Message),
    /// Any other implementation block item.
    Other(syn::ImplItem),
}

impl quote::ToTokens for ImplItem {
    /// We mainly implement this trait for this pro! type to have a derived
    /// [`Spanned`](`syn::spanned::Spanned`) implementation for it.
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Constructor(constructor) => constructor.to_tokens(tokens),
            Self::Message(message) => message.to_tokens(tokens),
            Self::Other(other) => other.to_tokens(tokens),
        }
    }
}

impl TryFrom<syn::ImplItem> for ImplItem {
    type Error = syn::Error;

    fn try_from(impl_item: syn::ImplItem) -> Result<Self, Self::Error> {
        match impl_item {
            syn::ImplItem::Method(method_item) => {
                if !ir::contains_pro_attributes(&method_item.attrs) {
                    return Ok(Self::Other(method_item.into()))
                }
                let attr = ir::first_pro_attribute(&method_item.attrs)?
                    .expect("missing expected pro! attribute for struct");
                match attr.first().kind() {
                    ir::AttributeArg::Message => {
                        <Message as TryFrom<_>>::try_from(method_item)
                            .map(Into::into)
                            .map(Self::Message)
                    }
                    ir::AttributeArg::Constructor => {
                        <Constructor as TryFrom<_>>::try_from(method_item)
                            .map(Into::into)
                            .map(Self::Constructor)
                    }
                    _ => Err(format_err_spanned!(
                        method_item,
                        "encountered invalid pro! attribute at this point, expected either \
                        #[pro(message)] or #[pro(constructor) attributes"
                    )),
                }
            }
            other_item => {
                // This is an error if the impl item contains any unexpected
                // pro! attributes. Otherwise it is a normal Rust item.
                if ir::contains_pro_attributes(other_item.attrs()) {
                    let (pro_attrs, _) =
                        ir::partition_attributes(other_item.attrs().iter().cloned())?;
                    assert!(!pro_attrs.is_empty());
                    fn into_err(attr: &ir::ProAttribute) -> syn::Error {
                        format_err!(attr.span(), "encountered unexpected pro! attribute",)
                    }
                    return Err(pro_attrs[1..]
                        .iter()
                        .map(into_err)
                        .fold(into_err(&pro_attrs[0]), |fst, snd| fst.into_combine(snd)))
                }
                Ok(Self::Other(other_item))
            }
        }
    }
}

impl ImplItem {
    /// Returns `true` if the impl block item is an pro! message.
    pub fn is_message(&self) -> bool {
        self.filter_map_message().is_some()
    }

    /// Returns `Some` if `self` is an pro! message.
    ///
    /// Otherwise, returns `None`.
    pub fn filter_map_message(&self) -> Option<&Message> {
        match self {
            ImplItem::Message(message) => Some(message),
            _ => None,
        }
    }

    /// Returns `true` if the impl block item is an pro! message.
    pub fn is_constructor(&self) -> bool {
        self.filter_map_constructor().is_some()
    }

    /// Returns `Some` if `self` is an pro! constructor.
    ///
    /// Otherwise, returns `None`.
    pub fn filter_map_constructor(&self) -> Option<&Constructor> {
        match self {
            ImplItem::Constructor(constructor) => Some(constructor),
            _ => None,
        }
    }

    /// Returns `true` if the impl block item is a non pro! specific item.
    pub fn is_other_item(&self) -> bool {
        self.filter_map_other_item().is_some()
    }

    /// Returns `Some` if `self` is a not an pro! specific item.
    ///
    /// Otherwise, returns `None`.
    pub fn filter_map_other_item(&self) -> Option<&syn::ImplItem> {
        match self {
            ImplItem::Other(rust_item) => Some(rust_item),
            _ => None,
        }
    }
}
