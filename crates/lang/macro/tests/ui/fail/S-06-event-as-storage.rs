use pro_lang as pro;

#[pro::contract]
mod event_as_storage {
    #[pro(event)]
    #[pro(storage)] // We cannot have #[pro(storage)] if we already have #[pro(event)]
    pub struct EventAsStorage {}

    impl EventAsStorage {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
