use pro_lang as pro;

#[pro::trait_definition]
pub trait Constructor {
    #[pro(constructor)]
    fn constructor() -> Self;
}

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    impl Constructor for Noop {
        #[pro(constructor, payable)]
        fn constructor() -> Self {
            Self {}
        }
    }

    impl Noop {
        #[pro(message)]
        pub fn noop(&self) {}
    }
}

fn main() {}
