# Lassie: Naturalization for the HOL4 tactic language

## Setup

- Download and install [the HOL4 interactive theorem prover](https://hol-theorem-prover.org/) with the [Poly/ML](https://polyml.org/) implementation of SML.
- Setup interactivity with HOL with either the Emacs mode or the Vim plugin.
- Set the environment variable `POLYDIR` to your `polyml` install folder (e.g. ~/git/polyml) and the variable `LASSIEDIR` to your `lassie` install folder (the directory containing this README).
- Launch an HOL session and open the Lassie structure (with `use` or `open`)
- Interface with Lassie using functions `Lassie.lassie`, `Lassie.nltac`, `Lassie.def` and `Lassie.accept`

