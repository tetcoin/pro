<div align="center">
    <img src="./.images/pro-logo-glow.svg" alt="pro!" height="136" />
<h1 align="center">
    Tetsy pro! for writing smart contracts
</h1>

[![codecov][c1]][c2] [![coveralls][d1]][d2] [![loc][e1]][e2] [![matrix][k1]][k2] [![discord][l1]][l2]

[a1]: https://gitlab.tetcoin.org/tetcoin/pro/badges/master/pipeline.svg
[a2]: https://gitlab.tetcoin.org/tetcoin/pro/pipelines?ref=master
[c1]: https://codecov.io/gh/tetcoin/pro/branch/master/graph/badge.svg
[c2]: https://codecov.io/gh/tetcoin/pro/branch/master
[d1]: https://coveralls.io/repos/github/tetcoin/pro/badge.svg?branch=master
[d2]: https://coveralls.io/github/tetcoin/pro?branch=master
[e1]: https://tokei.rs/b1/github/tetcoin/pro?category=code
[e2]: https://github.com/Aaronepower/tokei#badges
[f1]: https://img.shields.io/badge/click-blue.svg
[f2]: https://tetcoin.github.io/pro/pro_storage
[g1]: https://img.shields.io/badge/click-blue.svg
[g2]: https://tetcoin.github.io/pro/pro_env
[i1]: https://img.shields.io/badge/click-blue.svg
[i2]: https://tetcoin.github.io/pro/pro_prelude
[j1]: https://img.shields.io/badge/click-blue.svg
[j2]: https://tetcoin.github.io/pro/pro_lang
[k1]: https://img.shields.io/badge/matrix-chat-brightgreen.svg?style=flat
[k2]: https://riot.im/app/#/room/#pro:matrix.tetcoin.org
[l1]: https://img.shields.io/discord/722223075629727774?style=flat-square&label=discord
[l2]: https://discord.gg/ztCASQE

> <img src="./.images/pro-squid.svg" alt="squpro, the pro! mascot" style="vertical-align: middle" align="left" height="60" />pro! is an [eDSL](https://wiki.haskell.org/Embedded_domain_specific_language) to write WebAssembly based smart contracts using the Rust programming language. The compilation target are blockchains built on the [Substrate](https://github.com/tetcoin/substrate) framework.

<br/>

[Guided Tutorial for Beginners](https://substrate.dev/substrate-contracts-workshop/#/0/building-your-contract) •
[pro! Documentation Portal](https://tetcoin.github.io/pro-docs)

<br/>
</div>

More relevant lpros:
* Talk to us on [Element][k2] or [Discord][l2]
* [`cargo-contract`](https://github.com/tetcoin/cargo-contract) ‒ cli tool for pro! contracts
* [Canvas UI](https://tetcoin.github.io/canvas-ui/#/upload) ‒ webpage for contract deployment and interaction

## Table of Contents

* [Play with It](#play-with-it)
* [Usage](#usage)
* [Hello, World! ‒ The Flipper](#hello-world--the-flipper)
* [Examples](#examples)
* [How it Works](#how-it-works)
* [pro! Macros & Attributes Overview](#pro-macros--attributes-overview)
  * [Entry Point](#entry-point)
  * [Trait Definitions](#trait-definitions)
  * [Off-chain Testing](#off-chain-testing)
* [Developer Documentation](#developer-documentation)
* [Contributing](#contributing)
* [License](#license)


## Play with It

We have [a demonstration testnet](https://polkadot.js.org/apps/?rpc=wss%3A%2F%2Fcanvas-rpc.tetcoin.org) running.
You can request some tokens to play with from our [Faucet](https://riot.im/app/#/room/#canvas_faucet:matrix.tetcoin.org) and deploy your contracts via the [Canvas UI](https://tetcoin.github.io/canvas-ui/#/upload).

The [Canvas UI](https://tetcoin.github.io/canvas-ui/#/upload) can also be used to deploy your contract to e.g. a Substrate chain which you run locally and execute calls there.
If you want a quickstart you can use our [canvas-node](https://github.com/tetcoin/canvas-node#note) project.
It's a simple Substrate blockchain which is configured to include the Substrate module for smart contract functionality ‒ the `contracts` pallet (see [How it Works](#how-it-works) for more).

## Usage

A prerequisite for compiling smart contracts is to have Rust and Cargo installed. Here's [an installation guide](https://doc.rust-lang.org/cargo/getting-started/installation.html).

We recommend installing [`cargo-contract`](https://github.com/tetcoin/cargo-contract), a CLI tool for helping setting up and managing WebAssembly smart contracts written with pro!:

```
cargo install cargo-contract --force
```

Use the `--force` to ensure you are updated to the most recent `cargo-contract` version.

In order to initialize a new pro! project you can use:

```
cargo contract new flipper
```

This will create a folder `flipper` in your work directory.
The folder contains a scaffold `Cargo.toml` and a `lib.rs`, which both contain the necessary building blocks for using pro!.

The `lib.rs` contains our hello world contract ‒ the `Flipper`, which we explain in the next section.

In order to build the contract just execute these commands in the `flipper` folder:
```
cargo contract build
```

As a result you'll get a file `target/flipper.wasm` file, a `metadata.json` file and a `<contract-name>.contract` file in the `target` folder of your contract.
The `.contract` file combines the Wasm and metadata into one file and needs to be used when deploying the contract.


## Hello, World! ‒ The Flipper

The `Flipper` contract is a simple contract containing only a single `bool` value.
It provides methods to
* flip its value from `true` to `false` (and vice versa) and
* return the current state.


Below you can see the code using the `pro_lang` version of pro!.

```rust
use pro_lang as pro;

#[pro::contract]
mod flipper {
    /// The storage of the flipper contract.
    #[pro(storage)]
    pub struct Flipper {
        /// The single `bool` value.
        value: bool,
    }

    impl Flipper {
        /// Instantiates a new Flipper contract and initializes `value` to `init_value`.
        #[pro(constructor)]
        pub fn new(init_value: bool) -> Self {
            Self {
                value: init_value,
            }
        }

        /// Flips `value` from `true` to `false` or vice versa.
        #[pro(message)]
        pub fn flip(&mut self) {
            self.value = !self.value;
        }

        /// Returns the current state of `value`.
        #[pro(message)]
        pub fn get(&self) -> bool {
            self.value
        }
    }

    /// Simply execute `cargo test` in order to test your contract using the below unit tests.
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
```

Place this code in the `./lib.rs` file of your flipper contract and run `cargo contract build` to build your first pro! smart contract example.

## Examples

In the `examples` folder you'll find a number of examples written in pro!.

Some of the most interesting ones:

* `delegator` ‒ Implements cross-contract calling.
* `trait-erc20` ‒ Defines a trait for `Erc20` contracts and implements it.
* `erc721` ‒ An exemplary implementation of `Erc721` NFT tokens.
* `dns` ‒  A simple `DomainNameService` smart contract.
* …and more, just rummage through the folder 🙃.

To build a single example navigate to the root of the example and run:
```
cargo contract build
```

You should now have an optimized `<contract-name>.wasm` file and a `metadata.json` file in the `target` folder of the contract.

For further information, please have a look at the [Play with It](#play-with-it) section or our [smart contracts workshop](https://substrate.dev/substrate-contracts-workshop/).


## How it Works

* Substrate's [Framework for Runtime Aggregation of Modularised Entities (FRAME)](https://substrate.dev/docs/en/next/conceptual/runtime/frame) contains
a module  which implements an API for typical functions smart contracts need (storage, querying information about accounts, …).
This module is called the `contracts` pallet,
* The `contracts` pallet requires smart contracts to be uploaded to the blockchain as a Wasm blob.
* pro! is a smart contract language which targets the API exposed by `contracts`.
Hence pro! contracts are compiled to Wasm.
* When executing `cargo contract build` an additional file `metadata.json` is created.
It contains information about e.g. what methods the contract provides for others to call.

## pro! Macros & Attributes Overview

### Entry Point

In a module annotated with `#[pro::contract]` these attributes are available:

| Attribute | Where Applicable | Description |
|:--|:--|:--|
| `#[pro(storage)]` | On `struct` definitions. | Defines the pro! storage struct. There can only be one pro! storage definition per contract. |
| `#[pro(event)]` | On `struct` definitions. | Defines an pro! event. A contract can define multiple such pro! events. |
| `#[pro(anonymous)]` | Applicable to pro! events. | Tells the pro! codegen to treat the pro! event as anonymous which omits the event signature as topic upon emitting. Very similar to anonymous events in Solidity. |
| `#[pro(topic)]` | Applicate on pro! event field. | Tells the pro! codegen to provide a topic hash for the given field. Every pro! event can only have a limited number of such topic field. Similar semantics as to indexed event arguments in Solidity. |
| `#[pro(message)]` | Applicable to methods. | Flags a method for the pro! storage struct as message making it available to the API for calling the contract. |
| `#[pro(constructor)]` | Applicable to method. | Flags a method for the pro! storage struct as constructor making it available to the API for instantiating the contract. |
| `#[pro(payable)]` | Applicable to pro! messages. | Allows receiving value as part of the call of the pro! message. pro! constructors are implicitly payable. |
| `#[pro(selector = "..")]` | Applicable to pro! messages and pro! constructors. | Specifies a concrete dispatch selector for the flagged entity. This allows a contract author to precisely control the selectors of their APIs making it possible to rename their API without breakage. |
| `#[pro(namespace = "..")]` | Applicable to pro! trait implementation blocks. | Changes the resulting selectors of all the pro! messages and pro! constructors within the trait implementation. Allows to disambiguate between trait implementations with overlapping message or constructor names. Use only with great care and consideration! |
| `#[pro(impl)]` | Applicable to pro! implementation blocks. | Tells the pro! codegen that some implementation block shall be granted access to pro! internals even without it containing any pro! messages or pro! constructors. |

See [here](https://tetcoin.github.io/pro/pro_lang/attr.contract.html) for a more detailed description of those and also for details on the `#[pro::contract]` macro.

### Trait Definitions

Use`#[pro::trait_definition]` to define your very own trait definitions that are then implementable by pro! smart contracts.
See e.g. the [`examples/trait-erc20`](https://github.com/tetcoin/pro/blob/master/examples/trait-erc20/lib.rs#L49-L51) contract on how to utilize it or [the documentation](https://tetcoin.github.io/pro/pro_lang/attr.trait_definition.html) for details.

### Off-chain Testing

The `#[pro::test]` proc. macro enables off-chain testing. See e.g. the [`examples/erc20`](https://github.com/tetcoin/pro/blob/master/examples/erc20/lib.rs#L278-L280) contract on how to utilize those or [the documentation](https://tetcoin.github.io/pro/pro_lang/attr.test.html) for details.

## Developer Documentation

We have [a very comprehensive documentation portal](https://tetcoin.github.io/pro-docs),
but if you are looking for the crate level documentation itself, then these are
the relevant lpros:

| Crate | Docs | Description |
|:--|:--|:--|
`pro_lang` | [![][j1]][j2] | Language features expose by pro!. See [here](https://tetcoin.github.io/pro/pro_lang/attr.contract.html) for a detailed description of attributes which you can use in an `#[pro::contract]`. |
`pro_storage` | [![][f1]][f2] | Data structures available in pro!. |
`pro_env` | [![][g1]][g2] | Low-level interface for interacting with the smart contract Wasm executor. |
`pro_prelude` | [![][i1]][i2] | Common API for no_std and std to access alloc crate types. |


## Contributing

Visit our [contribution guidelines](CONTRIBUTING.md) for more information.

Use the scripts provided under `scripts/check-*` directory in order to run checks on either the workspace or all examples. Please do this before pushing work in a PR.

## License

The entire code within this repository is licensed under the [Apache License 2.0](LICENSE). Please [contact us](https://tetcoin.org/contact/) if you have questions about the licensing of our products.
