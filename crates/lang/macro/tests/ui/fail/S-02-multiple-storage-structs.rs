use pro_lang as pro;

#[pro::contract]
mod multiple_storage_structs {
    #[pro(storage)]
    pub struct FirstStorageStruct {}

    // pro! currently doesn't allow for multiple #[pro(storage)] structs
    #[pro(storage)]
    pub struct SecondStorageStruct {}

    impl FirstStorageStruct {
        #[pro(constructor)]
        pub fn constructor1() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message1(&self) {}
    }

    impl SecondStorageStruct {
        #[pro(constructor)]
        pub fn constructor2() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message2(&self) {}
    }
}

fn main() {}
