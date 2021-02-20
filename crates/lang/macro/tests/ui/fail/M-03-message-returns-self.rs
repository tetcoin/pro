use pro_lang as pro;

#[pro::contract]
mod message_returns_self {
    #[pro(storage)]
    pub struct MessageReturnsSelf {}

    impl MessageReturnsSelf {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn returns_self(&self) -> Self {}
    }
}

fn main() {}
