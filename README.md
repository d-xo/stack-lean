# stack-lean

This is an attempt to formalize the next-gen stack scheduling algorithm for the solidity compiler in
lean4.

An informal / human readable spec can be found here: https://notes.argot.org/vFBYW57jR6-uZD5xbK8aeg

## Setup

1. Run `nix develop` or install [elan](https://github.com/leanprover/elan).

2. Run the following:

```
lake update
lake exe cache get
```

## Developing

You can run `lean build` on the cli which will check all proofs, but for more involved dev work you
will want to setup an interactive environment. There are extensions for:

- [vscode](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) (officially supported)
- [neovim](https://github.com/Julian/lean.nvim)
- [emacs](https://github.com/leanprover-community/lean4-mode)
- [jetbrains](https://plugins.jetbrains.com/plugin/25104-lean4ij)
