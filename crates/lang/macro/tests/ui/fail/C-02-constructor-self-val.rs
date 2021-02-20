use pro_lang as pro;

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    impl Noop {
        #[pro(constructor)]
        pub fn invalid_self_val(self) -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn noop(&self) {}
    }
}

fn main() {}
