use pro_lang as pro;

#[pro::contract]
mod storage_as_event {
    #[pro(storage)]
    #[pro(event)] // We cannot have #[pro(event)] if we already have #[pro(storage)]
    pub struct StorageAsEvent {}

    impl StorageAsEvent {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
