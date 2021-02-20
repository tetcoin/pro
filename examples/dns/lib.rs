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

#![cfg_attr(not(feature = "std"), no_std)]

use pro_lang as pro;

#[pro::contract]
mod dns {
    #[cfg(not(feature = "pro-as-dependency"))]
    use pro_storage::{
        collections::hashmap::Entry,
        collections::HashMap as StorageHashMap,
        lazy::Lazy,
    };

    /// Emitted whenever a new name is being registered.
    #[pro(event)]
    pub struct Register {
        #[pro(topic)]
        name: Hash,
        #[pro(topic)]
        from: AccountId,
    }

    /// Emitted whenever an address changes.
    #[pro(event)]
    pub struct SetAddress {
        #[pro(topic)]
        name: Hash,
        from: AccountId,
        #[pro(topic)]
        old_address: Option<AccountId>,
        #[pro(topic)]
        new_address: AccountId,
    }

    /// Emitted whenver a name is being transferred.
    #[pro(event)]
    pub struct Transfer {
        #[pro(topic)]
        name: Hash,
        from: AccountId,
        #[pro(topic)]
        old_owner: Option<AccountId>,
        #[pro(topic)]
        new_owner: AccountId,
    }

    /// Domain name service contract inspired by ChainX's [blog post]
    /// (https://medium.com/@chainx_org/secure-and-decentralized-polkadot-domain-name-system-e06c35c2a48d).
    ///
    /// # Note
    ///
    /// This is a port from the blog post's pro! 1.0 based version of the contract
    /// to pro! 2.0.
    ///
    /// # Description
    ///
    /// The main function of this contract is domain name resolution which
    /// refers to the retrieval of numeric values corresponding to readable
    /// and easily memorable names such as “polka.dot” which can be used
    /// to facilitate transfers, voting and dapp-related operations instead
    /// of resorting to long IP addresses that are hard to remember.
    #[pro(storage)]
    #[derive(Default)]
    pub struct DomainNameService {
        /// A hashmap to store all name to addresses mapping.
        name_to_address: StorageHashMap<Hash, AccountId>,
        /// A hashmap to store all name to owners mapping.
        name_to_owner: StorageHashMap<Hash, AccountId>,
        /// The default address.
        default_address: Lazy<AccountId>,
    }

    /// Errors that can occur upon calling this contract.
    #[derive(Debug, PartialEq, Eq, scale::Encode, scale::Decode)]
    #[cfg_attr(feature = "std", derive(::tetsy_scale_info::TypeInfo))]
    pub enum Error {
        /// Returned if the name already exists upon registration.
        NameAlreadyExists,
        /// Returned if caller is not owner while required to.
        CallerIsNotOwner,
    }

    /// Type alias for the contract's result type.
    pub type Result<T> = core::result::Result<T, Error>;

    impl DomainNameService {
        /// Creates a new domain name service contract.
        #[pro(constructor)]
        pub fn new() -> Self {
            Default::default()
        }

        /// Register specific name with caller as owner.
        #[pro(message)]
        pub fn register(&mut self, name: Hash) -> Result<()> {
            let caller = self.env().caller();
            let entry = self.name_to_owner.entry(name);
            match entry {
                Entry::Occupied(_) => return Err(Error::NameAlreadyExists),
                Entry::Vacant(vacant) => {
                    vacant.insert(caller);
                    self.env().emit_event(Register { name, from: caller });
                }
            }
            Ok(())
        }

        /// Set address for specific name.
        #[pro(message)]
        pub fn set_address(&mut self, name: Hash, new_address: AccountId) -> Result<()> {
            let caller = self.env().caller();
            let owner = self.get_owner_or_default(name);
            if caller != owner {
                return Err(Error::CallerIsNotOwner)
            }
            let old_address = self.name_to_address.insert(name, new_address);
            self.env().emit_event(SetAddress {
                name,
                from: caller,
                old_address,
                new_address,
            });
            Ok(())
        }

        /// Transfer owner to another address.
        #[pro(message)]
        pub fn transfer(&mut self, name: Hash, to: AccountId) -> Result<()> {
            let caller = self.env().caller();
            let owner = self.get_owner_or_default(name);
            if caller != owner {
                return Err(Error::CallerIsNotOwner)
            }
            let old_owner = self.name_to_owner.insert(name, to);
            self.env().emit_event(Transfer {
                name,
                from: caller,
                old_owner,
                new_owner: to,
            });
            Ok(())
        }

        /// Get address for specific name.
        #[pro(message)]
        pub fn get_address(&self, name: Hash) -> AccountId {
            self.get_address_or_default(name)
        }

        /// Returns the owner given the hash or the default address.
        fn get_owner_or_default(&self, name: Hash) -> AccountId {
            *self
                .name_to_owner
                .get(&name)
                .unwrap_or(&*self.default_address)
        }

        /// Returns the address given the hash or the default address.
        fn get_address_or_default(&self, name: Hash) -> AccountId {
            *self
                .name_to_address
                .get(&name)
                .unwrap_or(&*self.default_address)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use pro_lang as pro;

        const DEFAULT_CALLEE_HASH: [u8; 32] = [0x07; 32];
        const DEFAULT_ENDOWMENT: Balance = 1_000_000;
        const DEFAULT_GAS_LIMIT: Balance = 1_000_000;

        fn default_accounts(
        ) -> pro_env::test::DefaultAccounts<pro_env::DefaultEnvironment> {
            pro_env::test::default_accounts::<pro_env::DefaultEnvironment>()
                .expect("off-chain environment should have been initialized already")
        }

        fn set_next_caller(caller: AccountId) {
            pro_env::test::push_execution_context::<pro_env::DefaultEnvironment>(
                caller,
                AccountId::from(DEFAULT_CALLEE_HASH),
                DEFAULT_ENDOWMENT,
                DEFAULT_GAS_LIMIT,
                pro_env::test::CallData::new(pro_env::call::Selector::new([0x00; 4])),
            )
        }

        #[pro::test]
        fn register_works() {
            let default_accounts = default_accounts();
            let name = Hash::from([0x99; 32]);

            set_next_caller(default_accounts.alice);
            let mut contract = DomainNameService::new();

            assert_eq!(contract.register(name), Ok(()));
            assert_eq!(contract.register(name), Err(Error::NameAlreadyExists));
        }

        #[pro::test]
        fn set_address_works() {
            let accounts = default_accounts();
            let name = Hash::from([0x99; 32]);

            set_next_caller(accounts.alice);

            let mut contract = DomainNameService::new();
            assert_eq!(contract.register(name), Ok(()));

            // Caller is not owner, `set_address` should fail.
            set_next_caller(accounts.bob);
            assert_eq!(
                contract.set_address(name, accounts.bob),
                Err(Error::CallerIsNotOwner)
            );

            // caller is owner, set_address will be successful
            set_next_caller(accounts.alice);
            assert_eq!(contract.set_address(name, accounts.bob), Ok(()));
            assert_eq!(contract.get_address(name), accounts.bob);
        }

        #[pro::test]
        fn transfer_works() {
            let accounts = default_accounts();
            let name = Hash::from([0x99; 32]);

            set_next_caller(accounts.alice);

            let mut contract = DomainNameService::new();
            assert_eq!(contract.register(name), Ok(()));

            // Test transfer of owner.
            assert_eq!(contract.transfer(name, accounts.bob), Ok(()));

            // Owner is bob, alice `set_address` should fail.
            assert_eq!(
                contract.set_address(name, accounts.bob),
                Err(Error::CallerIsNotOwner)
            );

            set_next_caller(accounts.bob);
            // Now owner is bob, `set_address` should be successful.
            assert_eq!(contract.set_address(name, accounts.bob), Ok(()));
            assert_eq!(contract.get_address(name), accounts.bob);
        }
    }
}
