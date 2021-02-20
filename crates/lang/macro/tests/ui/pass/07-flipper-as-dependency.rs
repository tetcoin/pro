use pro_lang as pro;

#[pro::contract(compile_as_dependency = true)]
mod flipper {
    #[pro(storage)]
    pub struct Flipper {
        value: bool,
    }

    impl Flipper {
        #[pro(constructor)]
        pub fn new(init_value: bool) -> Self {
            Self { value: init_value }
        }

        #[pro(constructor)]
        pub fn default() -> Self {
            Self::new(false)
        }

        #[pro(message)]
        pub fn flip(&mut self) {
            self.value = !self.value;
        }

        #[pro(message)]
        pub fn get(&self) -> bool {
            self.value
        }
    }
}

fn main() {}
