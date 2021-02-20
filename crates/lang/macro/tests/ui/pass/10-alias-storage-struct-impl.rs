use pro_lang as pro;

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    pub type NoopAlias = Noop;

    impl NoopAlias {
        #[pro(constructor)]
        pub fn new() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn noop(&self) {}
    }
}

fn main() {}
