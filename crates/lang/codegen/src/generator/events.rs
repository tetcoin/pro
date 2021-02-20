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
    generator,
    GenerateCode,
    GenerateCodeUsing as _,
};
use derive_more::From;
use proc_macro2::{
    Span,
    TokenStream as TokenStream2,
};
use quote::{
    quote,
    quote_spanned,
};
use syn::spanned::Spanned as _;

/// Generates code for the pro! event structs of the contract.
#[derive(From)]
pub struct Events<'a> {
    contract: &'a ir::Contract,
}

impl AsRef<ir::Contract> for Events<'_> {
    fn as_ref(&self) -> &ir::Contract {
        self.contract
    }
}

impl GenerateCode for Events<'_> {
    fn generate_code(&self) -> TokenStream2 {
        if self.contract.module().events().next().is_none() {
            // Generate no code in case there are no event definitions.
            return TokenStream2::new()
        }
        let emit_event_trait_impl = self.generate_emit_event_trait_impl();
        let event_base = self.generate_event_base();
        let topic_guards = self.generate_topic_guards();
        let topics_impls = self.generate_topics_impls();
        let event_structs = self.generate_event_structs();
        quote! {
            #emit_event_trait_impl
            #event_base
            #( #topic_guards )*
            #( #event_structs )*
            #( #topics_impls )*
        }
    }
}

impl<'a> Events<'a> {
    /// Used to allow emitting user defined events directly instead of converting
    /// them first into the automatically generated base trait of the contract.
    fn generate_emit_event_trait_impl(&self) -> TokenStream2 {
        let storage_ident = &self.contract.module().storage().ident();
        let no_cross_calling_cfg =
            self.generate_code_using::<generator::CrossCallingConflictCfg>();
        quote! {
            const _: () = {
                #no_cross_calling_cfg
                impl<'a> ::pro_lang::EmitEvent<#storage_ident> for ::pro_lang::EnvAccess<'a, Environment> {
                    fn emit_event<E>(self, event: E)
                    where
                        E: Into<<#storage_ident as ::pro_lang::BaseEvent>::Type>,
                    {
                        ::pro_env::emit_event::<
                            Environment,
                            <#storage_ident as ::pro_lang::BaseEvent>::Type
                        >(event.into());
                    }
                }
            };
        }
    }

    /// Generates the base event enum that comprises all user defined events.
    /// All emitted events are converted into a variant of this enum before being
    /// serialized and emitted to apply their unique event discriminant (ID).
    fn generate_event_base(&self) -> TokenStream2 {
        let storage_ident = &self.contract.module().storage().ident();
        let no_cross_calling_cfg =
            self.generate_code_using::<generator::CrossCallingConflictCfg>();
        let event_idents = self
            .contract
            .module()
            .events()
            .map(|event| event.ident())
            .collect::<Vec<_>>();
        let base_event_ident =
            proc_macro2::Ident::new("__pro_EventBase", Span::call_site());
        quote! {
            #no_cross_calling_cfg
            #[derive(::scale::Encode, ::scale::Decode)]
            pub enum #base_event_ident {
                #( #event_idents(#event_idents), )*
            }

            #no_cross_calling_cfg
            const _: () = {
                impl ::pro_lang::BaseEvent for #storage_ident {
                    type Type = #base_event_ident;
                }
            };

            #(
                #no_cross_calling_cfg
                const _: () = {
                    impl From<#event_idents> for #base_event_ident {
                        fn from(event: #event_idents) -> Self {
                            Self::#event_idents(event)
                        }
                    }
                };
            )*

            const _: () = {
                pub enum __pro_UndefinedAmountOfTopics {}
                impl ::pro_env::topics::EventTopicsAmount for __pro_UndefinedAmountOfTopics {
                    const AMOUNT: usize = 0;
                }

                #no_cross_calling_cfg
                impl ::pro_env::Topics for #base_event_ident {
                    type RemainingTopics = __pro_UndefinedAmountOfTopics;

                    fn topics<E, B>(
                        &self,
                        builder: ::pro_env::topics::TopicsBuilder<::pro_env::topics::state::Uninit, E, B>,
                    ) -> <B as ::pro_env::topics::TopicsBuilderBackend<E>>::Output
                    where
                        E: ::pro_env::Environment,
                        B: ::pro_env::topics::TopicsBuilderBackend<E>,
                    {
                        match self {
                            #(
                                Self::#event_idents(event) => {
                                    <#event_idents as ::pro_env::Topics>::topics::<E, B>(event, builder)
                                }
                            )*
                        }
                    }
                }
            };
        }
    }

    /// Generate checks to guard against too many topics in event definitions.
    fn generate_topics_guard(&self, event: &ir::Event) -> TokenStream2 {
        let storage_ident = self.contract.module().storage().ident();
        let event_ident = event.ident();
        let len_topics = event.fields().filter(|event| event.is_topic).count();
        let span = event.span();
        quote_spanned!(span=>
            const _: () = {
                #[allow(non_camel_case_types)]
                pub enum __pro_CheckSatisfied {}
                pub enum EventTopicsWithinBounds {}
                impl ::pro_lang::True for __pro_CheckSatisfied {}
                #[doc(hidden)]
                pub trait CompliesWithTopicLimit {}
                impl CompliesWithTopicLimit for __pro_CheckSatisfied {}

                #[allow(non_camel_case_types)]
                pub trait __pro_RenameBool {
                    type Type;
                }
                impl __pro_RenameBool for [(); true as usize] {
                    type Type = __pro_CheckSatisfied;
                }
                impl __pro_RenameBool for [(); false as usize] {
                    type Type = #event_ident;
                }

                #[allow(non_upper_case_globals)]
                const __pro_MAX_EVENT_TOPICS: usize = <
                    <#storage_ident as ::pro_lang::ContractEnv>::Env as ::pro_env::Environment
                >::MAX_EVENT_TOPICS;

                fn __pro_ensure_max_event_topics<T>(_: T)
                where
                    T: __pro_RenameBool,
                    <T as __pro_RenameBool>::Type: CompliesWithTopicLimit,
                {}
                let _ = __pro_ensure_max_event_topics::<[(); (#len_topics <= __pro_MAX_EVENT_TOPICS) as usize]>;
            };
        )
    }

    /// Generates the guard code that protects against having too many topics defined on an pro! event.
    fn generate_topic_guards(&'a self) -> impl Iterator<Item = TokenStream2> + 'a {
        let no_cross_calling_cfg =
            self.generate_code_using::<generator::CrossCallingConflictCfg>();
        self.contract.module().events().map(move |event| {
            let span = event.span();
            let topics_guard = self.generate_topics_guard(event);
            quote_spanned!(span =>
                #no_cross_calling_cfg
                #topics_guard
            )
        })
    }

    /// Generates the `Topics` trait implementations for the user defined events.
    fn generate_topics_impls(&'a self) -> impl Iterator<Item = TokenStream2> + 'a {
        let no_cross_calling_cfg =
            self.generate_code_using::<generator::CrossCallingConflictCfg>();
        let contract_ident = self.contract.module().storage().ident();
        self.contract.module().events().map(move |event| {
            let span = event.span();
            let event_ident = event.ident();
            let event_signature = syn::LitByteStr::new(
                format!("{}::{}", contract_ident, event_ident
            ).as_bytes(), span);
            let len_event_signature = event_signature.value().len();
            let len_topics = event.fields().filter(|field| field.is_topic).count();
            let topic_impls = event
                .fields()
                .enumerate()
                .filter(|(_, field)| field.is_topic)
                .map(|(n, topic_field)| {
                    let span = topic_field.span();
                    let field_ident = topic_field
                        .ident()
                        .map(quote::ToTokens::into_token_stream)
                        .unwrap_or_else(|| quote_spanned!(span => #n));
                    let field_type = topic_field.ty();
                    let signature = syn::LitByteStr::new(
                        format!("{}::{}::{}", contract_ident, event_ident,
                            field_ident
                        ).as_bytes(), span);
                    quote_spanned!(span =>
                        .push_topic::<::pro_env::topics::PrefixedValue<#field_type>>(
                            &::pro_env::topics::PrefixedValue { value: &self.#field_ident, prefix: #signature }
                        )
                    )
                });
            // Only include topic for event signature in case of non-anonymous event.
            let event_signature_topic = match event.anonymous {
                true => None,
                false => Some(quote_spanned!(span=>
                    .push_topic::<::pro_env::topics::PrefixedValue<[u8; #len_event_signature]>>(
                        &::pro_env::topics::PrefixedValue { value: #event_signature, prefix: b"" }
                    )
                ))
            };
            // Anonymous events require 1 fewer topics since they do not include their signature.
            let anonymous_topics_offset = if event.anonymous { 0 } else { 1 };
            let remaining_topics_ty = match len_topics + anonymous_topics_offset {
                0 => quote_spanned!(span=> ::pro_env::topics::state::NoRemainingTopics),
                n => quote_spanned!(span=> [::pro_env::topics::state::HasRemainingTopics; #n]),
            };
            quote_spanned!(span =>
                #no_cross_calling_cfg
                const _: () = {
                    impl ::pro_env::Topics for #event_ident {
                        type RemainingTopics = #remaining_topics_ty;

                        fn topics<E, B>(
                            &self,
                            builder: ::pro_env::topics::TopicsBuilder<::pro_env::topics::state::Uninit, E, B>,
                        ) -> <B as ::pro_env::topics::TopicsBuilderBackend<E>>::Output
                        where
                            E: ::pro_env::Environment,
                            B: ::pro_env::topics::TopicsBuilderBackend<E>,
                        {
                            builder
                                .build::<Self>()
                                #event_signature_topic
                                #(
                                    #topic_impls
                                )*
                                .finish()
                        }
                    }
                };
            )
        })
    }

    /// Generates all the user defined event struct definitions.
    fn generate_event_structs(&'a self) -> impl Iterator<Item = TokenStream2> + 'a {
        let no_cross_calling_cfg =
            self.generate_code_using::<generator::CrossCallingConflictCfg>();
        self.contract.module().events().map(move |event| {
            let span = event.span();
            let ident = event.ident();
            let attrs = event.attrs();
            let fields = event.fields().map(|event_field| {
                let span = event_field.span();
                let attrs = event_field.attrs();
                let vis = event_field.vis();
                let ident = event_field.ident();
                let ty = event_field.ty();
                quote_spanned!(span=>
                    #( #attrs )*
                    #vis #ident : #ty
                )
            });
            quote_spanned!(span =>
                #no_cross_calling_cfg
                #( #attrs )*
                #[derive(scale::Encode, scale::Decode)]
                pub struct #ident {
                    #( #fields ),*
                }
            )
        })
    }
}
