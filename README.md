# tick-tock-CSP et al.
This repository contains a mechanised version of the tick-tock CSP model, as well as its encoding in FDR for model-checking.
In addition, it contains ongoing work related to the mechanisation of a prioritisation operator in tick-tock, and its 
relationship with the Pri of the Finite-Linear model.

The theory files contained here target Isabelle2018. A ROOT file exists that contains several sessions corresponding to
the major models described below.

## Models
There are two major CSP models contained in this repository, namely:

* FL: Contains the Finite-Linear model.
* Tick-Tock: Contains the tick-tock model.

## Other results
* Tick-Tock-FL: Contains the mechanisation of a stepwise Galois connection between FL and Tick-Tock.

## Auxiliary theories
* Utils: Defines a type of partial orders as used for defining prioritisation operators over regular events.

