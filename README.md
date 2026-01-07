# `clash-num`

This is a (very) WIP crate to add support for some of the primitive numeric or number-like types in
the [Clash hardware description language][clash] to Rust. This crate does have fairly complete
documentation, so for more information on the goings-on and how things work, please refer to that.

# Development

This crate is set up to use Nix flakes, and includes a `.envrc` to take advantage of that. It also
makes use of [Tarpaulin][tarpaulin] for code coverage.

# Future work

Beyond the future work in the [`lib.rs` documentation][libdocs], here's the important things to be
done before this crate can be treated as properly useable, and not just a WIP experiment.
- Tests need to be written in `signed.rs` and `unsigned.rs`
- Optimisations for `BitVec<N>` should be considered, since in some embedded environments doing
  memory access is expensive. As such, limiting those should be considered. One such way to do this
  would be to treat a `[u8; N]` as more like a `(&[u8], &[usize], &[u8])`, where the "center" part
  of the array is treated as a `usize`-aligned slice of `usize`s, and any primitive ops are done on
  those instead of on `u8`s. Any remaining `u8`s outside of this word-aligned region should then be
  handled on their own separately. This should reduce the number of memory accesses by quite a lot,
  but was not included in this crate for reasons of time scoping.
- Code coverage should be increased. At time of writing, tests cover only around 70% of the lines of
  code in the repository, and 0 of the lines in the signed and unsigned files. These numbers should
  be much higher, closer to (or at) 100%.

# License

`clash-num` is licensed under the Apache License (Version 2.0). See `LICENSE` for more details.

[clash]: https://clash-lang.org/
[libdocs]: https://github.com/QBayLogic/clash-num/blob/main/src/lib.rs#L4-L468
[tarpaulin]: https://github.com/xd009642/tarpaulin
