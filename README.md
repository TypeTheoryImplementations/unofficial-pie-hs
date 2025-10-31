# <p align="center"> Unofficial-Pie-Haskell </p>

<p align="center">
<a href="https://www.gnu.org/licenses/agpl-3.0">
  <img src="https://img.shields.io/badge/License-AGPL_v3-green.svg" alt="License: AGPL v3"></img>
</a>
</p>

## What is Pie?

Pie is the dependently typed programming language from the excellent book [The Little Typer](https://thelittletyper.com/).
Pie supports the following:
- `Pi` types (as well as non-dependent versions)
- `Sigma` types (as well as non-dependent versions)
- Id types (aka `=` types) as well as associated eliminators including the J-eliminator
- `Nat`, `List`, and `Vec` as well as their associated eliminators
- The MLTT-derived judgmental/definitional equality rules
- A single predicative type universe `U`
- `Either` (aka sum types)
- `Trivial` (1-element type) and `Absurd` (0-element type)

It is an interpreted statically-typed language primarily designed to be used as a pedagogical proof assistant.

I have no relation to Pie or The Little Typer. I read the book and thought it would be fun to reimplement the language in Haskell (the reference implementation is in Racket). I discovered a few bugs and inefficiencies in the process that are fixed in my version. My version intentionally does not implement `TODO`. Additionally, while it has error reporting, it has no editor integration and its errors are significantly less detailed than the reference Racket implementation.

## What is next?

This was my first foray into static type systems after implementing the Simply-Typed Lambda Calculus. My next plan is to either learn web dev and make a [Godbolt.org](https://godbolt.org/) inspired code playground, or I might fork and extend my Pie implementation to support full Martin-Lof Dependent Type Theory and possibly even Cubical Types. As far as I know, the only things it's missing to be MLTT are an infinite predicative type universe hierarchy and general inductive types (or at least W-types if I don't want to go that far). If I decide to explore cubical types, it will likely be by adding a CHM (Cohen–Huber–Mortberg)-based type system based on [cubicaltt](https://github.com/mortberg/cubicaltt) after I read the [HoTT book](https://homotopytypetheory.org/book/).

## What is the license for this code?

This is **not** a clean-room implementation. As such, I have licensed my code under the same license as the reference implementation of Pie: [the GNU Affero General Public License version 3](https://www.gnu.org/licenses/agpl-3.0). All Haskell code in `src/` and `src-public` is licensed as such.
Regarding code within `tests/pie/`, any files **not** beginning with `TestProgram` and/or located within the `bookTests/` directory are derivatives of code examples from *The Little Typer* and are thus licensed under the [CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/deed.en) license. All other code within this repository is dual-licensed as both public domain (BSD 0-Clause) and AGPL-3.0 unless otherwise stated to the fullest extent of the law. All files should have a copyright notice at the top specifying the license.

Copies of both licenses can be found in the `LICENSES/` directory.

Additionally, older commits have a placeholder auto-generated `LICENSE` file that uses BSD 3-clause. These versions were never distributed prior to the commit that adds the proper licenses. As such, please disregard prior commits that are licensed improperly, not just because they're buggy and incorrect, but because they are retroactively licensed the same as this commit.

## How to use?

This is a standard Haskell cabal package, so it can be cloned, built, and ran like any other cabal package.

The program accepts a list of Pie source file names and outputs whether or not they are valid. An example for how to use can be found in the `runTests.sh` shell script if on Linux.
