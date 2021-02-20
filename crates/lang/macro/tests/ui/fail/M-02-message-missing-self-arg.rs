use pro_lang as pro;

#[pro::contract]
mod missing_message_self_arg {
    #[pro(storage)]
    pub struct MissingMessageSelfArg {}

    impl MissingMessage {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn missing_self_arg() {}
    }
}

fn main() {}
