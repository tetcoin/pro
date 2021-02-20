use pro_lang as pro;

#[pro::contract(dynamic_storage_allocator = "foo")]
mod invalid_version {
    #[pro(storage)]
    pub struct InvalidVersion {}

    impl InvalidVersion {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
