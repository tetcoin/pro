use pro_lang as pro;

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    impl Noop {
        #[pro(constructor)]
        pub fn new() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn noop(&self) {}
    }

    struct NonProStruct {}
    enum NonProEnum {}
    impl NonProStruct {
        fn do_nothing() {}
    }

    type NonProTypeAlias = u32;
}

fn main() {}
