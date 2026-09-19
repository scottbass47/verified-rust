# Verified data structures and algorithms

This project collects executable Rust data structures and algorithms together
with their Verus specifications and proofs. Each implementation lives in its
own file under `src/` and is exported from `src/lib.rs`.

## Implementations

- `sorted_set.rs`: a sorted, duplicate-free set backed by `Vec<i64>`, with
  verified binary search, insertion, and removal.
- `binary_heap.rs`: planned next.

## Tooling bootstrap

After Rust and the Verus release are installed:

```sh
cd ~/Documents/formal-verification/data-structures-and-algorithms
cargo add vstd
cargo check
cargo verus verify
```

In Neovim, use `<leader>rv` to run `cargo verus verify` in a split,
`<leader>rc` for `cargo check`, and `<leader>rf` to format with `verusfmt`.
