use pro_lang as pro;

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    impl Noop {
        #[pro(constructor, payable)]
        pub fn abi_constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn noop(&self) {}
    }
}

fn main() {}
