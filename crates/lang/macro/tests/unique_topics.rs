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
mod my_contract {
    #[pro(storage)]
    pub struct MyContract {}

    /// Exemplary event
    #[pro(event)]
    pub struct MyEvent {
        #[pro(topic)]
        v0: Option<AccountId>,
        #[pro(topic)]
        v1: Balance,
        #[pro(topic)]
        v2: bool,
        #[pro(topic)]
        v3: bool,
    }

    impl MyContract {
        /// Creates a new `MyContract` instance.
        #[pro(constructor)]
        pub fn new() -> Self {
            MyContract {}
        }

        /// Emits a `MyEvent`.
        #[pro(message)]
        pub fn emit_my_event(&self) {
            Self::env().emit_event(MyEvent {
                v0: None,
                v1: 0,
                v2: false,
                v3: false,
            });
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use pro_env::test::EmittedEvent;
        use pro_lang as pro;

        #[pro::test]
        fn event_must_have_unique_topics() {
            // given
            let my_contract = MyContract::new();

            // when
            MyContract::emit_my_event(&my_contract);

            // then
            // all topics must be unique
            let emitted_events =
                pro_env::test::recorded_events().collect::<Vec<EmittedEvent>>();
            let mut encoded_topics: std::vec::Vec<&[u8]> = emitted_events[0]
                .topics
                .iter()
                .map(|topic| topic.encoded_bytes().expect("encoded bytes must exist"))
                .collect();
            assert!(!has_duplicates(&mut encoded_topics));
        }
    }

    /// Finds duplicates in a given vector.
    ///
    /// This function has complexity of `O(n * log n)` and no additional memory
    /// is required, although the order of items is not preserved.
    fn has_duplicates<T: PartialEq + AsRef<[u8]>>(items: &mut Vec<T>) -> bool {
        // Sort the vector
        items.sort_by(|a, b| Ord::cmp(a.as_ref(), b.as_ref()));
        // And then find any two consecutive equal elements.
        items.windows(2).any(|w| {
            match w {
                &[ref a, ref b] => a == b,
                _ => false,
            }
        })
    }
}
