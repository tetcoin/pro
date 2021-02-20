use pro_lang as pro;

#[pro::contract]
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

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn it_works() {
            let mut flipper = Flipper::new(false);
            assert_eq!(flipper.get(), false);
            flipper.flip();
            assert_eq!(flipper.get(), true);
        }
    }
}

fn main() {}
