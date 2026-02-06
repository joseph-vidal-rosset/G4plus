# G4+ — Automated Theorem Prover for Minimal, Intuitionistic, and Classical Logic

G4+ is a unified automated theorem prover that implements the G4 sequent calculus system for three logical frameworks: minimal logic, intuitionistic logic, and classical logic.

## Features

- **Unified proof system**: Single calculus handles all three logics
- **Multiple proof formats**: 
  - Sequent calculus (bussproofs)
  - Natural deduction (Fitch-style flag notation)
  - Natural deduction (tree-style)
- **Cross-validation**: Integrates nanoCoP for proof verification
- **TPTP support**: Compatible with standard theorem proving formats
- **Web interface**: Built on SWI-Prolog's tinker framework

## Quick Start

Load the prover:
```prolog
?- [prover_loader].
```

Prove a formula:
```prolog
?- prove([a => b, a] > [b]).
?- prove([a & b] <> [b & a]).
```

## Architecture

The prover is organized into modular components:

1. `i_operators.pl` — Logical operator definitions
2. `ii_minimal_driver.pl` — nanoCoP integration
3. `iii_prover.pl` — Core G4 calculus engine
4. `iv_printer_sc.pl` — Sequent calculus output
5. `v_common_nd.pl` — Natural deduction utilities
6. `vi_flag_style.pl` — Fitch-style proof renderer
7. `vii_tree_style.pl` — Tree-style proof renderer
8. `viii_latex.pl` — LaTeX formatting
9. `ix_detections.pl` — Logic system detection
10. `x_tptp.pl` — TPTP format support

## Publication

A detailed description of the G4+ system and its theoretical foundations is under submission to the *Journal of Automated Reasoning*.

## License

MIT License — See LICENSE file for details.

## Built With Tinker

This prover uses [tinker](https://github.com/SWI-Prolog/tinker), a web-based interactive Prolog environment developed by Jan Wielemaker and the SWI-Prolog team.

---

**Author**: Joseph Vidal-Rosset  
**Institution**: Université de Lorraine, Nancy, France  
**Contact**: joseph@vidal-rosset.net
