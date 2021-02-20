use pro_lang as pro;

#[pro::contract]
mod incrementer {
    #[pro(storage)]
    pub struct Incrementer {
        value: i64,
    }

    #[pro(event)]
    pub struct Incremented {
        #[pro(topic)]
        caller: AccountId,
        #[pro(topic)]
        by: i32,
    }

    impl Incrementer {
        #[pro(constructor)]
        pub fn new(init_value: i32) -> Self {
            Self {
                value: init_value as i64,
            }
        }

        #[pro(constructor)]
        pub fn default() -> Self {
            Self::new(0)
        }

        #[pro(message)]
        pub fn inc_by(&mut self, by: i32) {
            let caller = self.env().caller();
            self.env().emit_event(Incremented { caller, by });
            self.value += by as i64;
        }

        #[pro(message)]
        pub fn get(&self) -> i64 {
            self.value
        }
    }
}

fn main() {}
