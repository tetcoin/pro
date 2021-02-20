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
    ast,
    ir,
};
use core::convert::TryFrom;
use proc_macro2::TokenStream as TokenStream2;

/// An pro! contract definition consisting of the pro! configuration and module.
///
/// This is the root of any pro! smart contract definition. It contains every
/// information accessible to the pro! smart contract macros. It is also used
/// as the root source for the pro! code generation.
///
/// # Example
///
/// ```no_compile
/// #[pro::contract(/* optional pro! configurations */)]
/// mod my_contract {
///     /* pro! and Rust definitions */
/// }
/// ```
pub struct Contract {
    /// The parsed Rust inline module.
    ///
    /// Contains all Rust module items after parsing. Note that while parsing
    /// the pro! module all pro! specific items are moved out of this AST based
    /// representation.
    item: ir::ItemMod,
    /// The specified pro! configuration.
    config: ir::Config,
}

impl Contract {
    /// Creates a new pro! contract from the given pro! configuration and module
    /// token streams.
    ///
    /// The pro! macro should use this constructor in order to setup pro!.
    ///
    /// # Note
    ///
    /// - The `pro_config` token stream must properly decode into [`ir::Config`].
    /// - The `pro_module` token stream must properly decode into [`ir::ItemMod`].
    ///
    /// # Errors
    ///
    /// Returns an error if the provided token stream cannot be decoded properly
    /// into a valid pro! configuration or pro! module respectively.
    pub fn new(
        pro_config: TokenStream2,
        pro_module: TokenStream2,
    ) -> Result<Self, syn::Error> {
        let config = syn::parse2::<ast::AttributeArgs>(pro_config)?;
        let module = syn::parse2::<syn::ItemMod>(pro_module)?;
        let pro_config = ir::Config::try_from(config)?;
        let pro_module = ir::ItemMod::try_from(module)?;
        Ok(Self {
            item: pro_module,
            config: pro_config,
        })
    }

    /// Returns the pro! inline module definition.
    ///
    /// # Note
    ///
    /// The pro! inline module definition is the module that comprises the
    /// whole pro! smart contract, e.g.:
    ///
    /// ```no_compile
    /// #[pro::contract]
    /// mod my_contract {
    ///     // ... definitions
    /// }
    /// ```
    pub fn module(&self) -> &ir::ItemMod {
        &self.item
    }

    /// Returns the configuration of the pro! smart contract.
    ///
    /// # Note
    ///
    /// The configuration is given via the `#[pro::contract(config))]` attribute
    /// macro annotation itself within the `(config)` part. The available fields
    /// are the following:
    ///
    /// - `types`: To specify `Environment` different from the default environment
    ///            types.
    /// - `storage-alloc`: If `true` enables the dynamic storage allocator
    ///                    facilities and code generation of the pro! smart
    ///                    contract. Does incure some overhead. The default is
    ///                    `true`.
    /// - `as-dependency`: If `true` compiles this pro! smart contract always as
    ///                    if it was a dependency of another smart contract.
    ///                    This configuration is mainly needed for testing and
    ///                    the default is `false`.
    ///
    /// Note that we might add more configuration fields in the future if
    /// necessary.
    pub fn config(&self) -> &ir::Config {
        &self.config
    }
}
