use pro_lang as pro;

#[pro::contract]
mod missing_message {
    #[pro(storage)]
    pub struct MissingMessage {}

    impl MissingMessage {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }
    }
}

fn main() {}
