use pro_lang as pro;

#[pro::contract]
mod forbidden_indents {
    #[pro(storage)]
    pub struct ForbiddenIndents {}

    impl ForbiddenIndents {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        /// An pro! message starting with __pro_ prefix.
        #[pro(message)]
        pub fn __pro_message(&self) {
            // All identifiers starting with `__pro_` are forbidden to use in pro!.
            let __pro_first = ();
        }
    }
}

fn main() {}
