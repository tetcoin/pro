use pro_lang as pro;

#[pro::contract]
mod message_invalid_selector {
    #[pro(storage)]
    pub struct MessageInvalidSelector {}

    impl MessageInvalidSelector {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message, selector = "0x00")]
        pub fn invalid_selector(&self) {}
    }
}

fn main() {}
