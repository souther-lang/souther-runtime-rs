# souther-runtime-rs

What Souther's Rust runtimes compute the same way, written once.

Souther has two backends whose runtimes are Rust: [souther-native-compiler](https://github.com/souther-lang/souther-native-compiler)
links one into a host-native library, and [souther-wasm-compiler](https://github.com/souther-lang/souther-wasm-compiler)
compiles one to the WebAssembly module every program is linked against. Neither depends on the
other. What both have to answer identically — because the language states the answer — lives here,
and each runtime reaches it as a git dependency pinned to a commit.

A crate here takes values and answers values. It has no arena, no address of either runtime's
width, no cell layout and no way of ending a run: a runtime keeps a value's parts where it keeps
things and decides what a failure ends the run as. Every crate is `no_std`, because the WebAssembly
runtime is.

Something moves here when it is the same computation written a second time, not before
(souther-native-compiler#8, #17).

## Crates

- `souther-exact`: exact arithmetic. The whole numbers a `Decimal` is worked out with, which of
  two neighbours a rounding mode answers, and the `Rational` that `/` answers — its one canonical
  form, the four operations, the order and the narrowings (spec §stdlib-rational). Moved from the
  native runtime when the WebAssembly runtime came to need the same `Rational`. And the `Decimal`
  itself (`Amount`): what each operation on one answers, the widest whole number one holds, and
  the text it is written as (spec §primitives, §stdlib-decimal). Moved from the native runtime
  when the WebAssembly runtime's own copy turned out to hold no widest whole number.

## Depending on it

```toml
[dependencies]
souther-exact = { git = "https://github.com/souther-lang/souther-runtime-rs", rev = "<commit>" }
```

A commit and not a branch, so that moving to a newer one is a change of what the runtime computes
that a commit of the runtime says.

What the commit fixes is this repository's source, which is what states the answers. It does not
fix the versions of the crates that source depends on: a library's `Cargo.lock` binds nothing
downstream, so each runtime resolves `num-bigint` and the rest in its own lock, and two runtimes on
one commit can hold different patch releases of them. That is allowed on purpose. What they are
asked for is whole-number arithmetic, whose answers no correct release changes; an exact `=`
requirement would buy no different answer and would refuse every runtime whose other dependencies
asked for a neighbouring release. A runtime that wants the same release as another says so in its
own lock.

## Building

    cargo test
    cargo clippy --all-targets -- -D warnings
    cargo build --release --target wasm32v1-none

The toolchain is the one `rust-toolchain.toml` names. The crates build with the older Rust the
workspace's `rust-version` says, which CI checks.

## License

EPL-2.0
