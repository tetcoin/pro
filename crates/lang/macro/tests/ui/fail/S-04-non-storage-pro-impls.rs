use pro_lang as pro;

#[pro::contract]
mod non_storage_pro_impls {
    // This test ensures that pro! impl blocks are always
    // implemented on the only storage struct definition.

    #[pro(storage)]
    pub struct StorageStruct {}

    // This pro! impl block is okay.
    impl StorageStruct {
        #[pro(constructor)]
        pub fn constructor1() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message1(&self) {}
    }

    // Missing the #[pro(storage)] attribute on purpose.
    pub struct NonStorageStruct {}

    // This pro! impl block is invalid in that it implements
    // the messages and constructors for a non-existing pro!
    // storage struct. We expect a failure here.
    impl NonStorageStruct {
        #[pro(constructor)]
        pub fn constructor2() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message2(&self) {}
    }
}

fn main() {}
