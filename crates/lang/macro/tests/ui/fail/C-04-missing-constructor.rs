use pro_lang as pro;

#[pro::contract]
mod noop {
    #[pro(storage)]
    pub struct Noop {}

    impl Noop {
        #[pro(message)]
        pub fn noop(&self) {}
    }
}

fn main() {}
