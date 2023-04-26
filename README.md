# Artifact for "TreeSync: Authenticated Group Management for Messaging Layer Security"

## Link to the paper

[Cryptology ePrint Archive](https://eprint.iacr.org/2022/1732)

## Structure of the repository

- comparse: external support library for parsers and serializers, imported, not part of this work
- dolev-yao-star: external support library for Dolev-Yao reasoning in F*, imported, not part of this work
- mls-star: this work

## Functions, types, and theorems from the paper

Section 3.1: TreeSync data structures

- [common tree type](mls-star/fstar/common/code/MLS.Tree.fst#L46)
- [parent node type](mls-star/fstar/treesync/code/MLS.TreeSync.NetworkTypes.fst#L272)
- [leaf node type](mls-star/fstar/treesync/code/MLS.TreeSync.NetworkTypes.fst#L155)
- [treesync type](mls-star/fstar/treesync/code/MLS.TreeSync.Types.fst#L8)
- [mls bytes](mls-star/fstar/common/code/MLS.NetworkTypes.fst#L28)

Section 3.2: TreeSync operations

- [path update / apply path](mls-star/fstar/treesync/code/MLS.TreeSync.Operations.fst#L326)
- [remove](mls-star/fstar/common/code/MLS.TreeCommon.fst#L40)
- [add](mls-star/fstar/treesync/code/MLS.TreeSync.Operations.fst#L39)
- [parsing](comparse/src/Comparse.Parser.Typeclass.fst#L10)
- [serialization](comparse/src/Comparse.Parser.Typeclass.fst#L14)

Section 3.3: Tree Hash

- [tree hash](mls-star/fstar/treesync/code/MLS.TreeSync.TreeHash.fst#L62)

Section 3.4: Parent Hash

- [apply path loop](mls-star/fstar/treesync/code/MLS.TreeSync.Operations.fst#L298)
- [parent hash computation](mls-star/fstar/treesync/code/MLS.TreeSync.ParentHash.fst#L42)
- [parent hash verification](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst#L194)
- [revert add](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst#L59)

Section 4.1: TreeSync State Invariants

- [unmerged leaves invariant](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.UnmergedLeaves.fst#L48)
- [leaf signature valid](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ValidLeaves.fst#L15) and [verified by authentication service](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.AuthService.fst#L89) invariants
- [parent hash link](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst#L155)
- [parent hash invariant](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst#L194)
- [refined type for treesync](mls-star/fstar/treesync/code/MLS.TreeSync.Refined.Types.fst#L12)

Section 4.2: Verified Parsing and Serialization

- [correctness of serialization then parsing](comparse/src/Comparse.Parser.Typeclass.fst#L18)
- [correctness of parsing then serialization](comparse/src/Comparse.Parser.Typeclass.fst#L25)

Section 4.3: Tree Hash Integrity Lemma

- [tree hash integrity theorem](mls-star/fstar/treesync/proofs/MLS.TreeSync.TreeHash.Proofs.fst#L49)
- [tree hash input](mls-star/fstar/treesync/code/MLS.TreeSync.TreeHash.fst#L34)

Section 4.4: Parent Hash Integrity Lemma

- [revert add](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst#L59)
- [canonicalize](mls-star/fstar/treesync/proofs/MLS.TreeSync.Proofs.ParentHashGuarantees.fst#L64)
- [tree equivalence ](mls-star/fstar/treesync/proofs/MLS.TreeSync.Proofs.ParentHashGuarantees.fst#L74)
- [parent link integrity theorem](mls-star/fstar/treesync/proofs/MLS.TreeSync.Proofs.ParentHashGuarantees.fst#L572)

Section 4.5: TreeSync Authentication Theorem

- [leaf node signature predicate](mls-star/fstar/treesync/symbolic/MLS.TreeSync.Symbolic.LeafNodeSignature.fst#L135)
- [treesync authentication theorem](mls-star/fstar/treesync/symbolic/MLS.TreeSync.Symbolic.LeafNodeSignature.fst#L433)

## Build

There are three ways to build MLS*.

### Using nix (recommended)

This artifact is reproducible thanks to nix.
It uses the flakes feature, make sure to enable it.

    # This command will compile Z3, F*,
    # and the other dependencies to the correct version
    nix develop

    cd mls-star
    # This command will verify MLS*
    make
    # This command will run tests of MLS*, see last section of this README
    make check

### Using docker (recommended)

If nix is not installed on the system, it can be used through a docker image we provide.

    # Build the docker image. This will compile Z3 and F* to the correct version.
    docker build . -t treesync_artifact
    # Start the image and start a shell with correct environment
    docker run -it treesync_artifact

    cd mls-star
    # This command will verify MLS*
    make
    # This command will run tests of MLS*, see last section of this README
    make check

### Using a locally-installed F* (not recommended)

This artifact can also be built directly, assuming the host system has the correct dependencies.

This artifact is compatible with:
- F* commit eb911fc41d5ba730c15f2ac296ffc5ebf7b46560
- Z3 version 4.8.5
- OCaml version 4.14

However we can't guarantee everything will go smoothly with this method.

    # Change the PATH to have z3 and fstar.exe
    export PATH=$PATH:/path/to/z3/directory/bin:/path/to/fstar/directory/bin
    # Setup the environment
    export FSTAR_HOME=/path/to/fstar/directory
    eval $(opam env)

    cd mls-star
    # This command will verify MLS*
    make
    # This command will run tests of MLS*, see last section of this README
    make check

## Tour of the code

All of the MLS* code is located inside the directory mls-star/fstar.

### Specification

The common directory contains code and proofs shared between the different components of MLS*, with:
- [Cryptography typeclass](mls-star/fstar/common/code/MLS.Crypto.Builtins.fsti)
- [Common serializable types](mls-star/fstar/common/code/MLS.NetworkTypes.fst)
- [Result monad](mls-star/fstar/common/code/MLS.Result.fst)
- [Generic type for trees and paths](mls-star/fstar/common/code/MLS.Tree.fst)
- [Common operations on trees](mls-star/fstar/common/code/MLS.TreeCommon.fst)
- [And various associated lemmas](mls-star/fstar/common/proofs)

The treesync/code directory contains the TreeSync component code, with:
- [Serializable types from the RFC](mls-star/fstar/treesync/code/MLS.TreeSync.NetworkTypes.fst)
- [TreeSync's tree definition](mls-star/fstar/treesync/code/MLS.TreeSync.Types.fst)
- [Atomic operations on TreeSync's tree](mls-star/fstar/treesync/code/MLS.TreeSync.Operations.fst)
- [Tree hash computation](mls-star/fstar/treesync/code/MLS.TreeSync.TreeHash.fst)
- [Parent hash computation](mls-star/fstar/treesync/code/MLS.TreeSync.ParentHash.fst)
- [Invariant on unmerged leaves](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.UnmergedLeaves.fst)
- [Invariant on parent hash](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ParentHash.fst)
- [Invariant on leaf signature validity](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.ValidLeaves.fst)
- [Invariant on authentication service](mls-star/fstar/treesync/code/MLS.TreeSync.Invariants.AuthService.fst)
- [A refined type for TreeSync's tree, enforcing the invariants](mls-star/fstar/treesync/code/MLS.TreeSync.Refined.Types.fst)
- [Atomic operations on the refined tree](mls-star/fstar/treesync/code/MLS.TreeSync.Refined.Operations.fst)
- [A type for TreeSync's state](mls-star/fstar/treesync/code/MLS.TreeSync.API.Types.fst)
- [Operations on TreeSync's state](mls-star/fstar/treesync/code/MLS.TreeSync.API.fst)

The treekem directory contains the TreeKEM component code, with:
- [Serializable types from the RFC](mls-star/fstar/treekem/MLS.TreeKEM.NetworkTypes.fst)
- [TreeKEM's tree definition](mls-star/fstar/treekem/MLS.TreeKEM.Types.fst)
- [Atomic operations on TreeKEM's tree](mls-star/fstar/treekem/MLS.TreeKEM.Operations.fst)
- [A type for TreeKEM's state](mls-star/fstar/treekem/MLS.TreeKEM.API.Types.fst)
- [Operations on TreeKEM's state](mls-star/fstar/treekem/MLS.TreeKEM.API.fst)

The treedem directory contains the TreeDEM component code, with:
- [Serializable types from the RFC](mls-star/fstar/treedem/MLS.TreeDEM.NetworkTypes.fst)
- [Implementation of the key schedule](mls-star/fstar/treedem/MLS.TreeDEM.Keys.fst)
- [Types for the message content](mls-star/fstar/treedem/MLS.TreeDEM.Message.Content.fst)
- [Types for the message framing](mls-star/fstar/treedem/MLS.TreeDEM.Message.Types.fst)
- [Functions for the message framing](mls-star/fstar/treedem/MLS.TreeDEM.Message.Framing.fst)
- [Computation of the transcript hash](mls-star/fstar/treedem/MLS.TreeDEM.Message.Transcript.fst)
- [Implementation of PSKs](mls-star/fstar/treedem/MLS.TreeDEM.PSK.fst)
- [Processing of the Welcome message](mls-star/fstar/treedem/MLS.TreeDEM.Welcome.fst)

The glue directory contains glue code, with:
- [glue between the network and TreeSync/TreeKEM types](mls-star/fstar/glue/MLS.NetworkBinder.fst)
- [glue between TreeSync and TreeKEM](mls-star/fstar/glue/MLS.TreeSyncTreeKEMBinder.fst)

The api directory contains a simplified high-level API combining everything, with:
- [a simplified interface](mls-star/fstar/api/MLS.fsti)
- [the implementation of this interface](mls-star/fstar/api/MLS.fst)

### Proofs

- [glue code and alternative DY* interface](mls-star/fstar/symbolic/MLS.Symbolic.fst)
- [generic code to make global predicates from local ones](mls-star/fstar/symbolic/MLS.Symbolic.SplitPredicate.fst)
- [interface for sessions, using local predicates](mls-star/fstar/symbolic/MLS.Symbolic.Session.fst)
- [interface for typed sessions (not just bytes)](mls-star/fstar/symbolic/MLS.Symbolic.TypedSession.fst)
- [generic session to implement a key/value dictionnary](mls-star/fstar/symbolic/MLS.Symbolic.MapSession.fst)
- [parser definitions useful for the symbolic proofs](mls-star/fstar/symbolic/MLS.Symbolic.Parsers.fst)

The treesync/proofs directory contains invariant proofs and all various hash integrity theorems, with:
- [Invariant proof for unmerged leaves](mls-star/fstar/treesync/proofs/MLS.TreeSync.Invariants.UnmergedLeaves.Proofs.fst)
- [Invariant proof for parent hash](mls-star/fstar/treesync/proofs/MLS.TreeSync.Invariants.ParentHash.Proofs.fst)
- [Invariant proof for leaf signature validity](mls-star/fstar/treesync/proofs/MLS.TreeSync.Invariants.ValidLeaves.Proofs.fst)
- [Invariant proof for authentication service](mls-star/fstar/treesync/proofs/MLS.TreeSync.Invariants.AuthService.Proofs.fst)
- [Tree hash integrity proof](mls-star/fstar/treesync/proofs/MLS.TreeSync.TreeHash.Proofs.fst)
- [Parent hash integrity proof](mls-star/fstar/treesync/proofs/MLS.TreeSync.ParentHash.Proofs.fst)
- [Parent hash link integrity proof](mls-star/fstar/treesync/proofs/MLS.TreeSync.Proofs.ParentHashGuarantees.fst)

The treesync/symbolic directory contains all the symbolic proofs and API, with:
- [Leaf node signature guarantees](mls-star/fstar/treesync/symbolic/MLS.TreeSync.Symbolic.LeafNodeSignature.fst)
- [State type and invariants](mls-star/fstar/treesync/symbolic/MLS.TreeSync.Symbolic.API.Sessions.fst)
- [API exposing state modification](mls-star/fstar/treesync/symbolic/MLS.TreeSync.Symbolic.API.fst)
- and various other boilerplate code, either for the API or for the proofs

## What is tested with `make check`?

There are four types of tests:
- internal tests of the high-level API, which sends messages within a small group
- tests for the RFC test vectors
- fuzzer for the correctness of TreeKEM
- benchmarks

We pass all test vectors for the following ciphersuites:
- `MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519`
- `MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519`

If any of the test, fuzz or benchmark fails, the `make check` command will fail and the corresponding error is printed.

The test vectors comes from the [official repository](https://github.com/mlswg/mls-implementations), with the commit revision present in [this file](mls-star/test_vectors/git_commit).

