use pro_lang as pro;

#[pro::contract]
mod unknown_pro_marker_on_struct {
    #[pro(storage)]
    pub struct UnknownProMarkerOnStruct {}

    #[pro(unknown_or_unsupported)]
    pub struct HasUnknownMarker {}

    impl UnknownProMarkerOnStruct {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
