use pro_lang as pro;

#[pro::contract]
mod derive_for_storage {
    #[pro(storage)]
    #[derive(Default)]
    pub struct DeriveForStorage {}

    impl DeriveForStorage {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Default::default()
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
