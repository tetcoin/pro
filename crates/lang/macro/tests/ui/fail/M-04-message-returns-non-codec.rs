use pro_lang as pro;

#[pro::contract]
mod message_returns_non_codec {
    #[derive(tetsy_scale_info::TypeInfo)]
    pub struct NonCodec;

    #[pro(storage)]
    pub struct MessageReturnsNonCodecType {}

    impl MessageReturnsNonCodecType {
        #[pro(constructor)]
        pub fn constructor() -> Self {
            Self {}
        }

        #[pro(message)]
        pub fn returns_non_codec_type(&self) -> NonCodec {
            NonCodec
        }
    }
}

fn main() {}
