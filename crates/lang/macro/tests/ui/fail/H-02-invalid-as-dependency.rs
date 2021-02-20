use pro_lang as pro;

#[pro::contract(compile_as_dependency = "yes")]
mod invalid_as_dependency {
    #[pro(storage)]
    pub struct InvalidAsDependency {}

    impl InvalidAsDependency {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn message(&self) {}
    }
}

fn main() {}
