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

//! A smart contract which demonstrates behavior of the `self.env().terminate()`
//! function. It terminates itself once `terminate_me()` is called.

#![cfg_attr(not(feature = "std"), no_std)]
#![allow(clippy::new_without_default)]

use pro_lang as pro;

#[pro::contract]
pub mod just_terminates {
    /// No storage is needed for this simple contract.
    #[pro(storage)]
    pub struct JustTerminate {}

    impl JustTerminate {
        /// Creates a new instance of this contract.
        #[pro(constructor)]
        pub fn new() -> Self {
            Self {}
        }

        /// Terminates with the caller as beneficiary.
        #[pro(message)]
        pub fn terminate_me(&mut self) {
            self.env().terminate_contract(self.env().caller());
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        use pro_env::{
            call,
            test,
        };
        use pro_lang as pro;

        #[pro::test]
        fn terminating_works() {
            // given
            let accounts = default_accounts();
            let contract_id = pro_env::test::get_current_contract_account_id::<
                pro_env::DefaultEnvironment,
            >()
            .expect("Cannot get contract id");
            set_sender(accounts.alice);
            set_balance(contract_id, 100);
            let mut contract = JustTerminate::new();

            // when
            let should_terminate = move || contract.terminate_me();

            // then
            pro_env::test::assert_contract_termination::<pro_env::DefaultEnvironment, _>(
                should_terminate,
                accounts.alice,
                100,
            );
        }

        fn default_accounts(
        ) -> pro_env::test::DefaultAccounts<pro_env::DefaultEnvironment> {
            pro_env::test::default_accounts::<pro_env::DefaultEnvironment>()
                .expect("Off-chain environment should have been initialized already")
        }

        fn set_sender(sender: AccountId) {
            let callee = pro_env::account_id::<pro_env::DefaultEnvironment>()
                .unwrap_or([0x0; 32].into());
            test::push_execution_context::<Environment>(
                sender,
                callee,
                1000000,
                1000000,
                test::CallData::new(call::Selector::new([0x00; 4])), // dummy
            );
        }

        fn set_balance(account_id: AccountId, balance: Balance) {
            pro_env::test::set_account_balance::<pro_env::DefaultEnvironment>(
                account_id, balance,
            )
            .expect("Cannot set account balance");
        }
    }
}
