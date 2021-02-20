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

#![allow(dead_code)]

mod attrs;
mod chain_extension;
mod config;
mod contract;
mod idents_lint;
mod pro_test;
mod item;
mod item_impl;
mod item_mod;
mod selector;
mod trait_def;
pub mod utils;

#[cfg(test)]
use self::attrs::Attribute;

use self::attrs::{
    contains_pro_attributes,
    first_pro_attribute,
    partition_attributes,
    sanitize_attributes,
    AttributeArg,
    AttributeArgKind,
    AttributeFrag,
    ProAttribute,
};
pub use self::{
    attrs::Namespace,
    chain_extension::{
        ChainExtension,
        ChainExtensionMethod,
        ExtensionId,
    },
    config::Config,
    contract::Contract,
    pro_test::ProTest,
    item::{
        Event,
        ProItem,
        Item,
        Storage,
    },
    item_impl::{
        Callable,
        CallableKind,
        CallableWithSelector,
        Constructor,
        ImplItem,
        InputsIter,
        ItemImpl,
        IterConstructors,
        IterMessages,
        Message,
        Receiver,
        Visibility,
    },
    item_mod::{
        ItemMod,
        IterEvents,
        IterItemImpls,
    },
    selector::Selector,
    trait_def::{
        ProTrait,
        ProTraitConstructor,
        ProTraitItem,
        ProTraitMessage,
        IterProTraitItems,
    },
};
