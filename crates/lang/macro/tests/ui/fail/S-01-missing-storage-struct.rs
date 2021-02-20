use pro_lang as pro;

#[pro::contract]
mod missing_storage_struct {
    // We are missing the #[pro(storage)] attribute here
    pub struct MissingStorageStruct {}

    impl MissingStorageStruct {
        #[pro(constructor)]
        pub fn constructor() -> Self {}

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
