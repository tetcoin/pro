use pro_lang as pro;

#[pro::contract]
mod static_env {
    #[pro(storage)]
    pub struct UsesStaticEnv {}

    impl UsesStaticEnv {
        #[pro(constructor)]
        pub fn new() -> Self {
            assert!(Self::env().balance() > 0);
            Self {}
        }

        #[pro(message)]
        pub fn gas_left(&mut self) -> Balance {
            Self::env().gas_left()
        }
    }
}

fn main() {}
