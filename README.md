# Deforming (AdS_3 \times S^3 \times T^4) in Type IIB Supergravity

This repository contains Wolfram Language scripts that verify the Type IIB supergravity equations for the solutions presented in Section 5 of:

> Deforming AdS3 × S3 × T4 in Type IIB Supergravity
> Stefano Maurelli, Ruggero Noris, Marcelo Oyarzo, Mario Trigiante
> [arXiv:2603.XXXX [hep-th]](https://arxiv.org/abs/2603.XXXX)

The script `check_equations.wl` evaluates the Type IIB equations of motion on each solution.

---

## Requirements

* Wolfram Mathematica 14.3 or later

---

## Installation

Clone the repository:

```bash
git clone https://github.com/moyarzoca/typeIIB-warped-solutions-checks.git
cd typeIIB-warped-solutions-checks
```

---

## Execution

Run the main script from the terminal:

```bash
wolframscript -file check_equations.wl
```

Alternatively, open `check_equations.wl` in the Wolfram front end and evaluate it.

---

## Relation to the Paper

The repository is organized according to the three classes of solutions:

* Section 5.1 → `lightlike/`
* Section 5.2 → `spacelike/`
* Section 5.3 → `timelike/`

Each directory contains:

* `*_configuration.wl`
  Definition of the solution (metric, fluxes, dilaton) using differential forms.

* `equations.wl`
  Output produced by `check_equations.wl`, containing the evaluated equations of motion.

---

## Engine

Differential geometry and form computations are based on:

* PaillacoDiff
  (included locally in `PaillacoDiff.wl`, corresponding to tag `sparsearray-associations-migration-v0.1`)

The file `typeIIBequations.wl` defines the function:

```wl
stringIIBequations
```

This function takes as input an `Association` describing a Type IIB background (metric, fluxes, dilaton, assumptions) and returns:

* Dilaton equation
* NSNS (B_2) equation
* RR field equations
* Einstein equations

The script `check_equations.wl` evaluates these expressions on each solution and exports the results to the corresponding `equations.wl` file.

