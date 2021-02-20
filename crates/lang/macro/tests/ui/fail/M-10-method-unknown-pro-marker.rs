use pro_lang as pro;

#[pro::contract]
mod unknown_method_pro_marker {
    #[pro(storage)]
    pub struct UnknownMethodProMarker {}

    impl UnknownMethodProMarker {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}

        #[pro(unknown_marker)]
        pub fn method(&self) {}
    }
}

fn main() {}
