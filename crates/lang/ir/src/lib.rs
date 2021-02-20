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

//! The pro! intermediate representation (IR) and abstractions.
//!
//! This module defines everything the pro! procedural macro needs in order to
//! parse, analyze and generate code for pro! smart contracts.
//!
//! The entry point for every pro! smart contract is the [`Contract`](`crate::ir::Contract`)
//! with its [`Config`](`crate::ir::Config`) provided in the initial invocation at
//! `#[pro::contract(... configuration ...)]`.
//!
//! The pro! IR tries to stay close to the original Rust syntactic structure.
//! All pro! definitions of an pro! smart contract are always defined within
//! a so-called Rust inline modlue (`mod my_module { ... items ... }`).
//! Therefore all pro! definition are found and accessed using the
//! [`ItemMod`](`crate::ir::ItemMod`) data structure.

#[macro_use]
mod error;

mod ast;
mod ir;

pub use self::ir::{
    Callable,
    CallableKind,
    CallableWithSelector,
    ChainExtension,
    ChainExtensionMethod,
    Config,
    Constructor,
    Contract,
    Event,
    ExtensionId,
    ImplItem,
    ProItem,
    ProTest,
    ProTrait,
    ProTraitConstructor,
    ProTraitItem,
    ProTraitMessage,
    InputsIter,
    Item,
    ItemImpl,
    ItemMod,
    IterConstructors,
    IterEvents,
    IterProTraitItems,
    IterItemImpls,
    IterMessages,
    Message,
    Namespace,
    Receiver,
    Selector,
    Storage,
    Visibility,
};
