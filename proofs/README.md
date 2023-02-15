# Formalized Security Proof for Dilithium in the ROM

This developement is part of the suplementary material of the paper

            Fiat-Shamir with Aborts: Fixing and
        mechanizing the security proof of Dilithium

## Contents

The proofs are split over two directories. The `utils` directory
contains utility files that are not specific to the security proof of
Dilithium. This includes various extensions to the EasyCrypt libraries
(e.g., the yet-to-be-merged new matrix theory) and the games defining
assumptions like MLWE and SelfTargetMSIS.

The `security` directory contains the specification of Dilithium
together with the mechanized security proof. The key files are:

- `Dilithium.ec`: This is the top-level file, containing the
  specification of Dilithium, the security theorem for Dilithium
  (i.e., Theorem 4 from the paper), and a commented desciption of all
  the constants appearing in the security bound.

- `SimplifiedScheme.ec` : This file contains the simpified scheme
  (i.e., the one where the public key is (A,t)) and the proof of CMA
  security. This includes the proof of NMA security, the verification
  of the HVZK simulator, and the instantiation of the CMA-to-NMA
  reduction.

- `FSa_CMAtoKOA.eca`: This contains the proof of the CMA to NMA
  reduction (i.e., Theorem 3 from the paper). The file iself contains
  all the arguments corresponding to the proof of Lemma 1.

- `ReprogHybrid.eca`: This file contains the core arguments for the
  CMA to NMA reduction: bounding the loss of the combined hop from
  `Prog` to `Trans` (i.e., essentially the proof of Theorem 3).

- `DRing.eca`: The abstract theory specifying the minimal structure (on
  Rq, highBits, etc.) required to carry out the security proof.

- `ConcreteDRing.eca` an instance of `DRing`, showing that the ring Rq
  from the specification of Dilithium has all the properties needed in
  the security proof.


## Testing

Checking all the proofs with EasyCrypt (EC) requires a development
version. This is mainly due to our use of the `expected-cost` logic
which is not yet part of the main development branch. Moreover, EC
requires certain versions of the SMT solvers Alt-Ergo, Z3, and CVC4 to
be available. To facilitate independent checking, we provide scripts
to set up a docker container with the entire toolchain.

### Docker

The configuration of docker is highly OS specific. On Linux, this
usually amounts to:

- installing docker and enabling the docker daemon
- adding the local user to the docker group
- rebooting (to let the group changes take effect)

### Test Script

If docker is configured correctly,

```
$ make tests
```

should set up a fresh Debian-based container, install the complete
EasyCrypt toolchain based on the `deploy-expected-cost` branch and run
`easycrypt` on all files in the development. Note that, depending on
your internet connection and hardware, the initial setup of the
container can take a while.

If desired, `make shell` provides a shell in the same context as the
tests. Note: Manually checking the files in the `security` folder
requires adding `-R utils` to the arguments of `easycrypt`.

### Local installation

Alternatively, EasyCrypt can be installed locally by following the
instructions at https://github.com/EasyCrypt/easycrypt

The only difference is that, when pinning easycrypt, the correct
branch needs to be chosen:

```
$ opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git#dilithium
```
