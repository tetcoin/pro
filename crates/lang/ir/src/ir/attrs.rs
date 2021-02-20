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
    error::ExtError as _,
    ir,
    ir::{
        ExtensionId,
        Selector,
    },
};
use core::{
    convert::TryFrom,
    result::Result,
};
use proc_macro2::{
    Ident,
    Span,
};
use regex::Regex;
use std::collections::HashMap;
use syn::spanned::Spanned;

/// Either an pro! specific attribute, or another uninterpreted attribute.
#[derive(Debug, PartialEq, Eq)]
pub enum Attribute {
    /// An pro! specific attribute, e.g. `#[pro(storage)]`.
    Pro(ProAttribute),
    /// Any other attribute.
    ///
    /// This can be a known `#[derive(Debug)]` or a specific attribute of another
    /// crate.
    Other(syn::Attribute),
}

/// Types implementing this trait can return a slice over their `syn` attributes.
pub trait Attrs {
    /// Returns the slice of attributes of an AST entity.
    fn attrs(&self) -> &[syn::Attribute];
}

impl Attrs for syn::ImplItem {
    fn attrs(&self) -> &[syn::Attribute] {
        match self {
            syn::ImplItem::Const(item) => &item.attrs,
            syn::ImplItem::Method(item) => &item.attrs,
            syn::ImplItem::Type(item) => &item.attrs,
            syn::ImplItem::Macro(item) => &item.attrs,
            _ => &[],
        }
    }
}

impl Attrs for syn::Item {
    fn attrs(&self) -> &[syn::Attribute] {
        use syn::Item;
        match self {
            Item::Const(syn::ItemConst { attrs, .. })
            | Item::Enum(syn::ItemEnum { attrs, .. })
            | Item::ExternCrate(syn::ItemExternCrate { attrs, .. })
            | Item::Fn(syn::ItemFn { attrs, .. })
            | Item::ForeignMod(syn::ItemForeignMod { attrs, .. })
            | Item::Impl(syn::ItemImpl { attrs, .. })
            | Item::Macro(syn::ItemMacro { attrs, .. })
            | Item::Macro2(syn::ItemMacro2 { attrs, .. })
            | Item::Mod(syn::ItemMod { attrs, .. })
            | Item::Static(syn::ItemStatic { attrs, .. })
            | Item::Struct(syn::ItemStruct { attrs, .. })
            | Item::Trait(syn::ItemTrait { attrs, .. })
            | Item::TraitAlias(syn::ItemTraitAlias { attrs, .. })
            | Item::Type(syn::ItemType { attrs, .. })
            | Item::Union(syn::ItemUnion { attrs, .. })
            | Item::Use(syn::ItemUse { attrs, .. }) => attrs,
            _ => &[],
        }
    }
}

/// An pro! specific attribute.
///
/// # Examples
///
/// An attribute with a simple flag:
/// ```no_compile
/// #[pro(storage)]
/// ```
///
/// An attribute with a parameterized flag:
/// ```no_compile
/// #[pro(selector = "0xDEADBEEF")]
/// ```
///
/// An attribute with multiple flags:
/// ```no_compile
/// #[pro(message, payable, selector = "0xDEADBEEF")]
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProAttribute {
    /// The internal non-empty sequence of arguments of the pro! attribute.
    args: Vec<AttributeFrag>,
}

impl Spanned for ProAttribute {
    fn span(&self) -> Span {
        self.args
            .iter()
            .map(|arg| arg.span())
            .fold(self.first().span(), |fst, snd| {
                fst.join(snd).unwrap_or_else(|| self.first().span())
            })
    }
}

impl ProAttribute {
    /// Ensure that the first pro! attribute argument is of expected kind.
    ///
    /// # Errors
    ///
    /// If the first pro! attribute argument is not of expected kind.
    pub fn ensure_first(&self, expected: &AttributeArgKind) -> Result<(), syn::Error> {
        if &self.first().arg.kind() != expected {
            return Err(format_err!(
                self.span(),
                "unexpected first pro! attribute argument",
            ))
        }
        Ok(())
    }

    /// Ensures that the given iterator of pro! attribute arguments do not have
    /// duplicates.
    ///
    /// # Errors
    ///
    /// If the given iterator yields duplicate pro! attribute arguments.
    fn ensure_no_duplicate_args<'a, A>(args: A) -> Result<(), syn::Error>
    where
        A: IntoIterator<Item = &'a ir::AttributeFrag>,
    {
        use crate::error::ExtError as _;
        use std::collections::HashSet;
        let mut seen: HashSet<&AttributeFrag> = HashSet::new();
        let mut seen2: HashMap<AttributeArgKind, Span> = HashMap::new();
        for arg in args.into_iter() {
            if let Some(seen) = seen.get(arg) {
                return Err(format_err!(
                    arg.span(),
                    "encountered duplicate pro! attribute arguments"
                )
                .into_combine(format_err!(
                    seen.span(),
                    "first equal pro! attribute argument here"
                )))
            }
            if let Some(seen) = seen2.get(&arg.kind().kind()) {
                return Err(format_err!(
                    arg.span(),
                    "encountered pro! attribute arguments with equal kinds"
                )
                .into_combine(format_err!(
                    *seen,
                    "first equal pro! attribute argument with equal kind here"
                )))
            }
            seen.insert(arg);
            seen2.insert(arg.kind().kind(), arg.span());
        }
        Ok(())
    }

    /// Converts a sequence of `#[pro(..)]` attributes into a single flattened
    /// `#[pro(..)]` attribute that contains all of the input arguments.
    ///
    /// # Example
    ///
    /// Given the input pro! attribute sequence `[ #[pro(message)], #[pro(payable)] ]`
    /// this procedure returns the single attribute `#[pro(message, payable)]`.
    ///
    /// # Errors
    ///
    /// - If the sequence of input pro! attributes contains duplicates.
    /// - If the input sequence is empty.
    pub fn from_expanded<A>(attrs: A) -> Result<Self, syn::Error>
    where
        A: IntoIterator<Item = Self>,
    {
        let args = attrs
            .into_iter()
            .map(|attr| attr.args)
            .flatten()
            .collect::<Vec<_>>();
        if args.is_empty() {
            return Err(format_err!(
                Span::call_site(),
                "encountered unexpected empty expanded pro! attribute arguments",
            ))
        }
        Self::ensure_no_duplicate_args(&args)?;
        Ok(Self { args })
    }

    /// Returns the first pro! attribute argument.
    pub fn first(&self) -> &AttributeFrag {
        self.args
            .first()
            .expect("encountered invalid empty pro! attribute list")
    }

    /// Returns an iterator over the non-empty flags of the pro! attribute.
    ///
    /// # Note
    ///
    /// This yields at least one pro! attribute flag.
    pub fn args(&self) -> ::core::slice::Iter<AttributeFrag> {
        self.args.iter()
    }

    /// Returns the namespace of the pro! attribute if any.
    pub fn namespace(&self) -> Option<ir::Namespace> {
        self.args().find_map(|arg| {
            if let ir::AttributeArg::Namespace(namespace) = arg.kind() {
                return Some(namespace.clone())
            }
            None
        })
    }

    /// Returns the selector of the pro! attribute if any.
    pub fn selector(&self) -> Option<ir::Selector> {
        self.args().find_map(|arg| {
            if let ir::AttributeArg::Selector(selector) = arg.kind() {
                return Some(*selector)
            }
            None
        })
    }

    /// Returns `true` if the pro! attribute contains the `payable` argument.
    pub fn is_payable(&self) -> bool {
        self.args()
            .any(|arg| matches!(arg.kind(), AttributeArg::Payable))
    }

    /// Returns `true` if the pro! attribute contains the `anonymous` argument.
    pub fn is_anonymous(&self) -> bool {
        self.args()
            .any(|arg| matches!(arg.kind(), AttributeArg::Anonymous))
    }

    /// Returns `false` if the pro! attribute contains the `handle_status = false` argument.
    ///
    /// Otherwise returns `true`.
    pub fn is_handle_status(&self) -> bool {
        !self
            .args()
            .any(|arg| matches!(arg.kind(), AttributeArg::HandleStatus(false)))
    }

    /// Returns `false` if the pro! attribute contains the `returns_result = false` argument.
    ///
    /// Otherwise returns `true`.
    pub fn is_returns_result(&self) -> bool {
        !self
            .args()
            .any(|arg| matches!(arg.kind(), AttributeArg::ReturnsResult(false)))
    }
}

/// An pro! specific attribute argument.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AttributeFrag {
    pub ast: syn::Meta,
    pub arg: AttributeArg,
}

impl AttributeFrag {
    /// Returns a shared reference to the attribute argument kind.
    pub fn kind(&self) -> &AttributeArg {
        &self.arg
    }
}

impl Spanned for AttributeFrag {
    fn span(&self) -> Span {
        self.ast.span()
    }
}

/// The kind of an pro! attribute argument.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeArgKind {
    /// `#[pro(storage)]`
    Storage,
    /// `#[pro(event)]`
    Event,
    /// `#[pro(anonymous)]`
    Anonymous,
    /// `#[pro(topic)]`
    Topic,
    /// `#[pro(message)]`
    Message,
    /// `#[pro(constructor)]`
    Constructor,
    /// `#[pro(payable)]`
    Payable,
    /// `#[pro(selector = "0xDEADBEEF")]`
    Selector,
    /// `#[pro(extension = N: u32)]`
    Extension,
    /// `#[pro(namespace = "my_namespace")]`
    Namespace,
    /// `#[pro(impl)]`
    Implementation,
    /// `#[pro(handle_status = flag: bool)]`
    HandleStatus,
    /// `#[pro(returns_result = flag: bool)]`
    ReturnsResult,
}

/// An pro! specific attribute flag.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeArg {
    /// `#[pro(storage)]`
    ///
    /// Applied on `struct` types in order to flag them for being the
    /// contract's storage definition.
    Storage,
    /// `#[pro(event)]`
    ///
    /// Applied on `struct` types in order to flag them for being an pro! event.
    Event,
    /// `#[pro(anonymous)]`
    ///
    /// Applied on `struct` event types in order to flag them as anonymous.
    /// Anonymous events have similar semantics as in Solidity in that their
    /// event signature won't be included in their event topics serialization
    /// to reduce event emitting overhead. This is especially useful for user
    /// defined events.
    Anonymous,
    /// `#[pro(topic)]`
    ///
    /// Applied on fields of pro! event types to indicate that they are topics.
    Topic,
    /// `#[pro(message)]`
    ///
    /// Applied on `&self` or `&mut self` methods to flag them for being an pro!
    /// exported message.
    Message,
    /// `#[pro(constructor)]`
    ///
    /// Applied on inherent methods returning `Self` to flag them for being pro!
    /// exported contract constructors.
    Constructor,
    /// `#[pro(payable)]`
    ///
    /// Applied on pro! constructors or messages in order to specify that they
    /// can receive funds from callers.
    Payable,
    /// `#[pro(selector = "0xDEADBEEF")]`
    ///
    /// Applied on pro! constructors or messages to manually control their
    /// selectors.
    Selector(Selector),
    /// `#[pro(namespace = "my_namespace")]`
    ///
    /// Applied on pro! trait implementation blocks to disambiguate other trait
    /// implementation blocks with equal names.
    Namespace(Namespace),
    /// `#[pro(impl)]`
    ///
    /// This attribute supports a niche case that is rarely needed.
    ///
    /// Can be applied on pro! implementation blocks in order to make pro! aware
    /// of them. This is useful if such an implementation block doesn't contain
    /// any other pro! attributes, so it would be flagged by pro! as a Rust item.
    /// Adding `#[pro(impl)]` on such implementation blocks makes them treated
    /// as pro! implementation blocks thus allowing to access the environment
    /// etc. Note that pro! messages and constructors still need to be explicitly
    /// flagged as such.
    Implementation,
    /// `#[pro(extension = N: u32)]`
    ///
    /// Applies on pro! chain extension method to set their `func_id` parameter.
    /// Every chain extension method must have exactly one pro! `extension` attribute.
    ///
    /// Used by the `#[pro::chain_extension]` proc. macro.
    Extension(ExtensionId),
    /// `#[pro(handle_status = flag: bool)]`
    ///
    /// Used by the `#[pro::chain_extension]` proc. macro.
    ///
    /// Default value: `true`
    HandleStatus(bool),
    /// `#[pro(returns_result = flag: bool)]`
    ///
    /// Used by the `#[pro::chain_extension]` proc. macro.
    ///
    /// Default value: `true`
    ReturnsResult(bool),
}

impl core::fmt::Display for AttributeArgKind {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        match self {
            Self::Storage => write!(f, "storage"),
            Self::Event => write!(f, "event"),
            Self::Anonymous => write!(f, "anonymous"),
            Self::Topic => write!(f, "topic"),
            Self::Message => write!(f, "message"),
            Self::Constructor => write!(f, "constructor"),
            Self::Payable => write!(f, "payable"),
            Self::Selector => {
                write!(f, "selector = S:[u8; 4]")
            }
            Self::Extension => {
                write!(f, "extension = N:u32)")
            }
            Self::Namespace => {
                write!(f, "namespace = N:string")
            }
            Self::Implementation => write!(f, "impl"),
            Self::HandleStatus => write!(f, "handle_status"),
            Self::ReturnsResult => write!(f, "returns_result"),
        }
    }
}

impl AttributeArg {
    /// Returns the kind of the pro! attribute argument.
    pub fn kind(&self) -> AttributeArgKind {
        match self {
            Self::Storage => AttributeArgKind::Storage,
            Self::Event => AttributeArgKind::Event,
            Self::Anonymous => AttributeArgKind::Anonymous,
            Self::Topic => AttributeArgKind::Topic,
            Self::Message => AttributeArgKind::Message,
            Self::Constructor => AttributeArgKind::Constructor,
            Self::Payable => AttributeArgKind::Payable,
            Self::Selector(_) => AttributeArgKind::Selector,
            Self::Extension(_) => AttributeArgKind::Extension,
            Self::Namespace(_) => AttributeArgKind::Namespace,
            Self::Implementation => AttributeArgKind::Implementation,
            Self::HandleStatus(_) => AttributeArgKind::HandleStatus,
            Self::ReturnsResult(_) => AttributeArgKind::ReturnsResult,
        }
    }
}

impl core::fmt::Display for AttributeArg {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> Result<(), core::fmt::Error> {
        match self {
            Self::Storage => write!(f, "storage"),
            Self::Event => write!(f, "event"),
            Self::Anonymous => write!(f, "anonymous"),
            Self::Topic => write!(f, "topic"),
            Self::Message => write!(f, "message"),
            Self::Constructor => write!(f, "constructor"),
            Self::Payable => write!(f, "payable"),
            Self::Selector(selector) => {
                write!(f, "selector = {:?}", selector.as_bytes())
            }
            Self::Extension(extension) => {
                write!(f, "extension = {:?}", extension.into_u32())
            }
            Self::Namespace(namespace) => {
                write!(f, "namespace = {:?}", namespace.as_bytes())
            }
            Self::Implementation => write!(f, "impl"),
            Self::HandleStatus(value) => write!(f, "handle_status = {:?}", value),
            Self::ReturnsResult(value) => write!(f, "returns_result = {:?}", value),
        }
    }
}

/// An pro! namespace applicable to a trait implementation block.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Namespace {
    /// The underlying bytes.
    bytes: Vec<u8>,
}

impl From<Vec<u8>> for Namespace {
    fn from(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }
}

impl Namespace {
    /// Returns the namespace as bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// Returns `true` if the given iterator yields at least one attribute of the form
/// `#[pro(..)]` or `#[pro]`.
///
/// # Note
///
/// This does not check at this point whether the pro! attribute is valid since
/// this check is optimized for efficiency.
pub fn contains_pro_attributes<'a, I>(attrs: I) -> bool
where
    I: IntoIterator<Item = &'a syn::Attribute>,
{
    attrs.into_iter().any(|attr| attr.path.is_ident("pro"))
}

/// Returns the first valid pro! attribute, if any.
///
/// Returns `None` if there are no pro! attributes.
///
/// # Errors
///
/// Returns an error if the first pro! attribute is invalid.
pub fn first_pro_attribute<'a, I>(
    attrs: I,
) -> Result<Option<ir::ProAttribute>, syn::Error>
where
    I: IntoIterator<Item = &'a syn::Attribute>,
{
    let first = attrs.into_iter().find(|attr| attr.path.is_ident("pro"));
    match first {
        None => Ok(None),
        Some(pro_attr) => ProAttribute::try_from(pro_attr.clone()).map(Some),
    }
}

/// Partitions the given attributes into pro! specific and non-pro! specific attributes.
///
/// # Error
///
/// Returns an error if some pro! specific attributes could not be successfully parsed.
pub fn partition_attributes<I>(
    attrs: I,
) -> Result<(Vec<ProAttribute>, Vec<syn::Attribute>), syn::Error>
where
    I: IntoIterator<Item = syn::Attribute>,
{
    use either::Either;
    use itertools::Itertools as _;
    let (pro_attrs, others) = attrs
        .into_iter()
        .map(<Attribute as TryFrom<_>>::try_from)
        .collect::<Result<Vec<Attribute>, syn::Error>>()?
        .into_iter()
        .partition_map(|attr| {
            match attr {
                Attribute::Pro(pro_attr) => Either::Left(pro_attr),
                Attribute::Other(other_attr) => Either::Right(other_attr),
            }
        });
    Attribute::ensure_no_duplicate_attrs(&pro_attrs)?;
    Ok((pro_attrs, others))
}

/// Sanitizes the given attributes.
///
/// This partitions the attributes into pro! and non-pro! attributes.
/// All pro! attributes are normalized, they are checked to have a valid first
/// pro! attribute argument and no conflicts given the conflict predicate.
///
/// Returns the partitioned pro! and non-pro! attributes.
///
/// # Parameters
///
/// The `is_conflicting_attr` closure returns `Ok` if the attribute does not conflict,
/// returns `Err(None)` if the attribute conflicts but without providing further reasoning
/// and `Err(Some(reason))` if the attribute conflicts given additional context information.
///
/// # Errors
///
/// - If there are invalid pro! attributes.
/// - If there are duplicate pro! attributes.
/// - If the first pro! attribute is not matching the expected.
/// - If there are conflicting pro! attributes.
pub fn sanitize_attributes<I, C>(
    parent_span: Span,
    attrs: I,
    is_valid_first: &ir::AttributeArgKind,
    mut is_conflicting_attr: C,
) -> Result<(ProAttribute, Vec<syn::Attribute>), syn::Error>
where
    I: IntoIterator<Item = syn::Attribute>,
    C: FnMut(&ir::AttributeFrag) -> Result<(), Option<syn::Error>>,
{
    let (pro_attrs, other_attrs) = ir::partition_attributes(attrs)?;
    let normalized = ir::ProAttribute::from_expanded(pro_attrs).map_err(|err| {
        err.into_combine(format_err!(parent_span, "at this invocation",))
    })?;
    normalized.ensure_first(is_valid_first).map_err(|err| {
        err.into_combine(format_err!(
            parent_span,
            "expected {} as first pro! attribute argument",
            is_valid_first,
        ))
    })?;
    normalized.ensure_no_conflicts(|arg| is_conflicting_attr(arg))?;
    Ok((normalized, other_attrs))
}

impl Attribute {
    /// Returns `Ok` if the given iterator yields no duplicate pro! attributes.
    ///
    /// # Errors
    ///
    /// If the given iterator yields duplicate pro! attributes.
    /// Note: Duplicate non-pro! attributes are fine.
    fn ensure_no_duplicate_attrs<'a, I>(attrs: I) -> Result<(), syn::Error>
    where
        I: IntoIterator<Item = &'a ProAttribute>,
    {
        use std::collections::HashSet;
        let mut seen: HashSet<&ProAttribute> = HashSet::new();
        for attr in attrs.into_iter() {
            if let Some(seen) = seen.get(attr) {
                use crate::error::ExtError as _;
                return Err(format_err!(
                    attr.span(),
                    "encountered duplicate pro! attribute"
                )
                .into_combine(format_err!(seen.span(), "first pro! attribute here")))
            }
            seen.insert(attr);
        }
        Ok(())
    }
}

impl TryFrom<syn::Attribute> for Attribute {
    type Error = syn::Error;

    fn try_from(attr: syn::Attribute) -> Result<Self, Self::Error> {
        if attr.path.is_ident("pro") {
            return <ProAttribute as TryFrom<_>>::try_from(attr).map(Into::into)
        }
        Ok(Attribute::Other(attr))
    }
}

impl From<ProAttribute> for Attribute {
    fn from(pro_attribute: ProAttribute) -> Self {
        Attribute::Pro(pro_attribute)
    }
}

impl TryFrom<syn::Attribute> for ProAttribute {
    type Error = syn::Error;

    fn try_from(attr: syn::Attribute) -> Result<Self, Self::Error> {
        if !attr.path.is_ident("pro") {
            return Err(format_err_spanned!(attr, "unexpected non-pro! attribute"))
        }
        match attr.parse_meta().map_err(|_| {
            format_err_spanned!(attr, "unexpected pro! attribute structure")
        })? {
            syn::Meta::List(meta_list) => {
                let args = meta_list
                    .nested
                    .into_iter()
                    .map(<AttributeFrag as TryFrom<_>>::try_from)
                    .collect::<Result<Vec<_>, syn::Error>>()?;
                Self::ensure_no_duplicate_args(&args)?;
                if args.is_empty() {
                    return Err(format_err_spanned!(
                        attr,
                        "encountered unsupported empty pro! attribute"
                    ))
                }
                Ok(ProAttribute { args })
            }
            _ => Err(format_err_spanned!(attr, "unknown pro! attribute")),
        }
    }
}

impl ProAttribute {
    /// Ensures that there are no conflicting pro! attribute arguments in `self`.
    ///
    /// The given `is_conflicting` describes for every pro! attribute argument
    /// found in `self` if it is in conflict.
    ///
    /// # Parameters
    ///
    /// The `is_conflicting_attr` closure returns `Ok` if the attribute does not conflict,
    /// returns `Err(None)` if the attribute conflicts but without providing further reasoning
    /// and `Err(Some(reason))` if the attribute conflicts given additional context information.
    pub fn ensure_no_conflicts<'a, P>(
        &'a self,
        mut is_conflicting: P,
    ) -> Result<(), syn::Error>
    where
        P: FnMut(&'a ir::AttributeFrag) -> Result<(), Option<syn::Error>>,
    {
        let mut err: Option<syn::Error> = None;
        for arg in self.args() {
            if let Err(reason) = is_conflicting(arg) {
                let conflict_err = format_err!(
                    arg.span(),
                    "encountered conflicting pro! attribute argument",
                );
                match &mut err {
                    Some(err) => {
                        err.combine(conflict_err);
                    }
                    None => {
                        err = Some(conflict_err);
                    }
                }
                if let Some(reason) = reason {
                    err.as_mut()
                        .expect("must be `Some` at this point")
                        .combine(reason);
                }
            }
        }
        if let Some(err) = err {
            return Err(err)
        }
        Ok(())
    }
}

/// Returns an error to notify about non-hex digits at a position.
fn err_non_hex(meta: &syn::Meta, pos: usize) -> syn::Error {
    format_err_spanned!(meta, "encountered non-hex digit at position {}", pos)
}

/// Returns an error to notify about an invalid pro! selector.
fn invalid_selector_err_regex(meta: &syn::Meta) -> syn::Error {
    format_err_spanned!(
        meta,
        "invalid selector - a selector must consist of four bytes in hex (e.g. `selector = \"0xCAFEBABE\"`)"
    )
}

impl TryFrom<syn::NestedMeta> for AttributeFrag {
    type Error = syn::Error;

    fn try_from(nested_meta: syn::NestedMeta) -> Result<Self, Self::Error> {
        match nested_meta {
            syn::NestedMeta::Meta(meta) => {
                match &meta {
                    syn::Meta::NameValue(name_value) => {
                        if name_value.path.is_ident("selector") {
                            if let syn::Lit::Str(lit_str) = &name_value.lit {
                                let regex = Regex::new(r"0x([\da-fA-F]{2})([\da-fA-F]{2})([\da-fA-F]{2})([\da-fA-F]{2})")
                                    .map_err(|_| {
                                    invalid_selector_err_regex(&meta)
                                })?;
                                let str = lit_str.value();
                                let cap =
                                    regex.captures(&str).ok_or_else(|| {
                                        invalid_selector_err_regex(&meta)
                                    })?;
                                if !regex.is_match(&str) {
                                    return Err(invalid_selector_err_regex(
                                        &meta,
                                    ))
                                }
                                let len_digits = (str.as_bytes().len() - 2) / 2;
                                if len_digits != 4 {
                                    return Err(format_err!(
                                            name_value,
                                            "expected 4-digit hexcode for `selector` argument, found {} digits",
                                            len_digits,
                                        ))
                                }
                                let selector_bytes = [
                                    u8::from_str_radix(&cap[1], 16)
                                        .map_err(|_| err_non_hex(&meta, 0))?,
                                    u8::from_str_radix(&cap[2], 16)
                                        .map_err(|_| err_non_hex(&meta, 1))?,
                                    u8::from_str_radix(&cap[3], 16)
                                        .map_err(|_| err_non_hex(&meta, 2))?,
                                    u8::from_str_radix(&cap[4], 16)
                                        .map_err(|_| err_non_hex(&meta, 3))?,
                                ];
                                return Ok(AttributeFrag {
                                    ast: meta,
                                    arg: AttributeArg::Selector(Selector::new(
                                        selector_bytes,
                                    )),
                                })
                            }
                            return Err(format_err!(name_value, "expecteded 4-digit hexcode for `selector` argument, e.g. #[pro(selector = 0xC0FEBABE]"))
                        }
                        if name_value.path.is_ident("namespace") {
                            if let syn::Lit::Str(lit_str) = &name_value.lit {
                                let bytes = lit_str.value().into_bytes();
                                return Ok(AttributeFrag {
                                    ast: meta,
                                    arg: AttributeArg::Namespace(
                                        Namespace::from(bytes),
                                    ),
                                })
                            }
                            return Err(format_err!(name_value, "expecteded string type for `namespace` argument, e.g. #[pro(namespace = \"hello\")]"))
                        }
                        if name_value.path.is_ident("extension") {
                            if let syn::Lit::Int(lit_int) = &name_value.lit {
                                let id = lit_int.base10_parse::<u32>().map_err(|parse_err| {
                                    format_err!(
                                        name_value,
                                        "could not parse `N` in `#[pro(extension = N)]` into a `u32` integer",
                                    ).into_combine(parse_err)
                                })?;
                                return Ok(AttributeFrag {
                                    ast: meta,
                                    arg: AttributeArg::Extension(
                                        ExtensionId::from_u32(id),
                                    ),
                                })
                            }
                            return Err(format_err!(name_value, "expecteded `u32` integer type for `N` in #[pro(extension = N)]"))
                        }
                        if name_value.path.is_ident("handle_status") {
                            if let syn::Lit::Bool(lit_bool) = &name_value.lit {
                                let value = lit_bool.value;
                                return Ok(AttributeFrag {
                                    ast: meta,
                                    arg: AttributeArg::HandleStatus(value),
                                })
                            }
                            return Err(format_err!(name_value, "expecteded `bool` value type for `flag` in #[pro(handle_status = flag)]"))
                        }
                        if name_value.path.is_ident("returns_result") {
                            if let syn::Lit::Bool(lit_bool) = &name_value.lit {
                                let value = lit_bool.value;
                                return Ok(AttributeFrag {
                                    ast: meta,
                                    arg: AttributeArg::ReturnsResult(value),
                                })
                            }
                            return Err(format_err!(name_value, "expecteded `bool` value type for `flag` in #[pro(returns_result = flag)]"))
                        }
                        Err(format_err_spanned!(
                            meta,
                            "unknown pro! attribute argument (name = value)",
                        ))
                    }
                    syn::Meta::Path(path) => {
                        path
                            .get_ident()
                            .map(Ident::to_string)
                            .ok_or_else(|| format_err_spanned!(meta, "unknown pro! attribute (path)"))
                            .and_then(|ident| match ident.as_str() {
                                "storage" => Ok(AttributeArg::Storage),
                                "message" => Ok(AttributeArg::Message),
                                "constructor" => Ok(AttributeArg::Constructor),
                                "event" => Ok(AttributeArg::Event),
                                "anonymous" => Ok(AttributeArg::Anonymous),
                                "topic" => Ok(AttributeArg::Topic),
                                "payable" => Ok(AttributeArg::Payable),
                                "impl" => Ok(AttributeArg::Implementation),
                                "namespace" => Err(format_err!(
                                    meta,
                                    "encountered #[pro(namespace)] that is missing its string parameter. \
                                    Did you mean #[pro(namespace = name: str)] ?"
                                )),
                                "extension" => Err(format_err!(
                                    meta,
                                    "encountered #[pro(extension)] that is missing its N parameter. \
                                    Did you mean #[pro(extension = N: u32)] ?"
                                )),
                                "handle_status" => Err(format_err!(
                                    meta,
                                    "encountered #[pro(handle_status)] that is missing its `flag: bool` parameter. \
                                    Did you mean #[pro(handle_status = flag: bool)] ?"
                                )),
                                "returns_result" => Err(format_err!(
                                    meta,
                                    "encountered #[pro(returns_result)] that is missing its `flag: bool` parameter. \
                                    Did you mean #[pro(returns_result = flag: bool)] ?"
                                )),
                                _ => Err(format_err_spanned!(
                                    meta, "unknown pro! attribute (path)"
                                ))
                            })
                            .map(|kind| AttributeFrag { ast: meta, arg: kind, })
                    }
                    syn::Meta::List(_) => {
                        Err(format_err_spanned!(
                            meta,
                            "unknown pro! attribute argument (list)"
                        ))
                    }
                }
            }
            syn::NestedMeta::Lit(_) => {
                Err(format_err_spanned!(
                    nested_meta,
                    "unknown pro! attribute argument (literal)"
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contains_pro_attributes_works() {
        assert!(!contains_pro_attributes(&[]));
        assert!(contains_pro_attributes(&[syn::parse_quote! { #[pro] }]));
        assert!(contains_pro_attributes(&[syn::parse_quote! { #[pro(..)] }]));
        assert!(contains_pro_attributes(&[
            syn::parse_quote! { #[inline] },
            syn::parse_quote! { #[likely] },
            syn::parse_quote! { #[pro(storage)] },
        ]));
        assert!(!contains_pro_attributes(&[
            syn::parse_quote! { #[inline] },
            syn::parse_quote! { #[likely] },
        ]));
    }

    /// Asserts that the given input yields the expected first argument or the
    /// expected error string.
    ///
    /// # Note
    ///
    /// Can be used to assert against the success and failure path.
    fn assert_first_pro_attribute(
        input: &[syn::Attribute],
        expected: Result<Option<Vec<ir::AttributeArg>>, &'static str>,
    ) {
        assert_eq!(
            first_pro_attribute(input)
                .map(|maybe_attr: Option<ir::ProAttribute>| {
                    maybe_attr.map(|attr: ir::ProAttribute| {
                        attr.args.into_iter().map(|arg| arg.arg).collect::<Vec<_>>()
                    })
                })
                .map_err(|err| err.to_string()),
            expected.map_err(ToString::to_string),
        )
    }

    #[test]
    fn first_pro_attribute_works() {
        assert_first_pro_attribute(&[], Ok(None));
        assert_first_pro_attribute(
            &[syn::parse_quote! { #[pro(storage)] }],
            Ok(Some(vec![AttributeArg::Storage])),
        );
        assert_first_pro_attribute(
            &[syn::parse_quote! { #[pro(invalid)] }],
            Err("unknown pro! attribute (path)"),
        );
    }

    mod test {
        use crate::ir;

        /// Mock for `ir::Attribute` to improve testability.
        #[derive(Debug, PartialEq, Eq)]
        pub enum Attribute {
            Pro(Vec<ir::AttributeArg>),
            Other(syn::Attribute),
        }

        impl From<ir::Attribute> for Attribute {
            fn from(attr: ir::Attribute) -> Self {
                match attr {
                    ir::Attribute::Pro(pro_attr) => {
                        Self::Pro(
                            pro_attr
                                .args
                                .into_iter()
                                .map(|arg| arg.arg)
                                .collect::<Vec<_>>(),
                        )
                    }
                    ir::Attribute::Other(other_attr) => Self::Other(other_attr),
                }
            }
        }

        impl From<ir::ProAttribute> for Attribute {
            fn from(pro_attr: ir::ProAttribute) -> Self {
                Attribute::from(ir::Attribute::Pro(pro_attr))
            }
        }

        /// Mock for `ir::ProAttribute` to improve testability.
        #[derive(Debug, PartialEq, Eq)]
        pub struct ProAttribute {
            args: Vec<ir::AttributeArg>,
        }

        impl From<ir::ProAttribute> for ProAttribute {
            fn from(pro_attr: ir::ProAttribute) -> Self {
                Self {
                    args: pro_attr
                        .args
                        .into_iter()
                        .map(|arg| arg.arg)
                        .collect::<Vec<_>>(),
                }
            }
        }

        impl<I> From<I> for ProAttribute
        where
            I: IntoIterator<Item = ir::AttributeArg>,
        {
            fn from(args: I) -> Self {
                Self {
                    args: args.into_iter().collect::<Vec<_>>(),
                }
            }
        }
    }

    /// Asserts that the given [`syn::Attribute`] is converted into the expected
    /// [`ir::Attribute]` or yields the expected error message.
    fn assert_attribute_try_from(
        input: syn::Attribute,
        expected: Result<test::Attribute, &'static str>,
    ) {
        assert_eq!(
            <ir::Attribute as TryFrom<_>>::try_from(input)
                .map(test::Attribute::from)
                .map_err(|err| err.to_string()),
            expected.map_err(ToString::to_string),
        )
    }

    #[test]
    fn storage_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(storage)]
            },
            Ok(test::Attribute::Pro(vec![AttributeArg::Storage])),
        );
    }

    /// This tests that `#[pro(impl)]` works which can be non-trivial since
    /// `impl` is also a Rust keyword.
    #[test]
    fn impl_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(impl)]
            },
            Ok(test::Attribute::Pro(vec![AttributeArg::Implementation])),
        );
    }

    #[test]
    fn selector_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(selector = "0xDEADBEEF")]
            },
            Ok(test::Attribute::Pro(vec![AttributeArg::Selector(
                Selector::new([0xDE, 0xAD, 0xBE, 0xEF]),
            )])),
        );
    }

    #[test]
    fn selector_non_hexcode() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(selector = "0xhelloworld")]
            },
            Err("invalid selector - a selector must consist of four bytes in hex (e.g. `selector = \"0xCAFEBABE\"`)"),
        );
    }

    #[test]
    fn selector_too_long() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(selector = "0xDEADBEEFC0FEBABE")]
            },
            Err("expected 4-digit hexcode for `selector` argument, found 8 digits"),
        );
    }

    #[test]
    fn selector_invalid_type() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(selector = 42)]
            },
            Err("expecteded 4-digit hexcode for `selector` argument, e.g. #[pro(selector = 0xC0FEBABE]"),
        );
    }

    #[test]
    fn namespace_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(namespace = "my_namespace")]
            },
            Ok(test::Attribute::Pro(vec![AttributeArg::Namespace(
                Namespace::from("my_namespace".to_string().into_bytes()),
            )])),
        );
    }

    #[test]
    fn namespace_invalid_type() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(namespace = 42)]
            },
            Err("expecteded string type for `namespace` argument, e.g. #[pro(namespace = \"hello\")]"),
        );
    }

    #[test]
    fn namespace_missing_parameter() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(namespace)]
            },
            Err(
                "encountered #[pro(namespace)] that is missing its string parameter. \
                Did you mean #[pro(namespace = name: str)] ?",
            ),
        );
    }

    #[test]
    fn extension_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(extension = 42)]
            },
            Ok(test::Attribute::Pro(vec![AttributeArg::Extension(
                ExtensionId::from_u32(42),
            )])),
        );
    }

    #[test]
    fn extension_invalid_value_type() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(extension = "string")]
            },
            Err("expecteded `u32` integer type for `N` in #[pro(extension = N)]"),
        );
    }

    #[test]
    fn extension_negative_integer() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(extension = -1)]
            },
            Err("could not parse `N` in `#[pro(extension = N)]` into a `u32` integer"),
        );
    }

    #[test]
    fn extension_too_big_integer() {
        let max_u32_plus_1 = (u32::MAX as u64) + 1;
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(extension = #max_u32_plus_1)]
            },
            Err("could not parse `N` in `#[pro(extension = N)]` into a `u32` integer"),
        );
    }

    #[test]
    fn extension_missing_parameter() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(extension)]
            },
            Err(
                "encountered #[pro(extension)] that is missing its N parameter. \
                Did you mean #[pro(extension = N: u32)] ?",
            ),
        );
    }

    #[test]
    fn handle_status_works() {
        fn expected_ok(value: bool) -> Result<test::Attribute, &'static str> {
            Ok(test::Attribute::Pro(vec![AttributeArg::HandleStatus(
                value,
            )]))
        }
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(handle_status = true)]
            },
            expected_ok(true),
        );
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(handle_status = false)]
            },
            expected_ok(false),
        );
    }

    #[test]
    fn handle_status_missing_parameter() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(handle_status)]
            },
            Err(
                "encountered #[pro(handle_status)] that is missing its `flag: bool` parameter. \
                Did you mean #[pro(handle_status = flag: bool)] ?",
            ),
        );
    }

    #[test]
    fn handle_status_invalid_parameter_type() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(handle_status = "string")]
            },
            Err(
                "expecteded `bool` value type for `flag` in #[pro(handle_status = flag)]",
            ),
        );
    }

    #[test]
    fn returns_result_works() {
        fn expected_ok(value: bool) -> Result<test::Attribute, &'static str> {
            Ok(test::Attribute::Pro(vec![AttributeArg::ReturnsResult(
                value,
            )]))
        }
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(returns_result = true)]
            },
            expected_ok(true),
        );
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(returns_result = false)]
            },
            expected_ok(false),
        );
    }

    #[test]
    fn returns_result_missing_parameter() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(returns_result)]
            },
            Err(
                "encountered #[pro(returns_result)] that is missing its `flag: bool` parameter. \
                Did you mean #[pro(returns_result = flag: bool)] ?",
            ),
        );
    }

    #[test]
    fn returns_result_invalid_parameter_type() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(returns_result = "string")]
            },
            Err("expecteded `bool` value type for `flag` in #[pro(returns_result = flag)]"),
        );
    }

    #[test]
    fn compound_mixed_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(message, namespace = "my_namespace")]
            },
            Ok(test::Attribute::Pro(vec![
                AttributeArg::Message,
                AttributeArg::Namespace(Namespace::from(
                    "my_namespace".to_string().into_bytes(),
                )),
            ])),
        )
    }

    #[test]
    fn compound_simple_works() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(
                    storage,
                    message,
                    constructor,
                    event,
                    topic,
                    payable,
                    impl,
                )]
            },
            Ok(test::Attribute::Pro(vec![
                AttributeArg::Storage,
                AttributeArg::Message,
                AttributeArg::Constructor,
                AttributeArg::Event,
                AttributeArg::Topic,
                AttributeArg::Payable,
                AttributeArg::Implementation,
            ])),
        );
    }

    #[test]
    fn non_pro_attribute_works() {
        let attr: syn::Attribute = syn::parse_quote! {
            #[non_pro(message)]
        };
        assert_attribute_try_from(attr.clone(), Ok(test::Attribute::Other(attr)));
    }

    #[test]
    fn empty_pro_attribute_fails() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro]
            },
            Err("unknown pro! attribute"),
        );
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro()]
            },
            Err("encountered unsupported empty pro! attribute"),
        );
    }

    #[test]
    fn duplicate_flags_fails() {
        assert_attribute_try_from(
            syn::parse_quote! {
                #[pro(message, message)]
            },
            Err("encountered duplicate pro! attribute arguments"),
        );
    }

    /// Asserts that the given sequence of [`syn::Attribute`] is correctly
    /// partitioned into the expected tuple of pro! and non-pro! attributes
    /// or that the expected error is returned.
    fn assert_parition_attributes(
        input: Vec<syn::Attribute>,
        expected: Result<(Vec<test::ProAttribute>, Vec<syn::Attribute>), &'static str>,
    ) {
        assert_eq!(
            partition_attributes(input)
                .map(|(pro_attr, other_attr)| {
                    (
                        pro_attr
                            .into_iter()
                            .map(test::ProAttribute::from)
                            .collect::<Vec<_>>(),
                        other_attr,
                    )
                })
                .map_err(|err| err.to_string()),
            expected.map_err(ToString::to_string)
        );
    }

    #[test]
    fn parition_attributes_works() {
        assert_parition_attributes(
            vec![
                syn::parse_quote! { #[pro(message)] },
                syn::parse_quote! { #[non_pro_attribute] },
            ],
            Ok((
                vec![test::ProAttribute::from(vec![AttributeArg::Message])],
                vec![syn::parse_quote! { #[non_pro_attribute] }],
            )),
        )
    }

    #[test]
    fn parition_duplicates_fails() {
        assert_parition_attributes(
            vec![
                syn::parse_quote! { #[pro(message)] },
                syn::parse_quote! { #[pro(message)] },
            ],
            Err("encountered duplicate pro! attribute"),
        )
    }
}
