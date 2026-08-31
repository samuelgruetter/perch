## 🐟 PERCH: Proving Execution Restrictions and Control-flow Hardening

The goal of this project is to formally verify software-enforced privilege levels.
Using binary verifiers such as Binsweep [2] that analyze a binary before it is run, we can check that it only contains instructions from an allow-list, and thus enforce that a program does not access certain resources.
Possible use cases include lightweight sandboxing such as HypoVisor [3].
However, on architectures with variable instruction lengths, programs that jump into the middle of an instruction could start executing instructions that were never intended to be executed, so it is important to enforce control-flow integrity.
And for protecting memory regions, features like memory-protection keys (MPK) can be used, as long as one makes sure that the program to be isolated does not run any `WRPKRU` instruction (which modifies the protection registers).
However, it is very tricky to get all the details right, as described in the "PKU pitfalls" paper [1].
Therefore, we want to write machine-checked proofs that the policies implemented by binary verifiers indeed achieve the desired guarantees.

### Build

It is recommended to browse and edit the files using VS Code. The [Lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) can install the right Lean version (as given in `./lean-toolchain`) as well as the dependencies (currently just the [Kraken x86 semantics](https://github.com/AeneasVerif/kraken)).

`lake` is Lean's build tool, and `elan` is used to manage different Lean versions. Both of these can be installed from within the VS Code Lean extension.

To build the project, run `lake build`.


### References

* [1] Connor et. al, SEC'20: *PKU pitfalls: attacks on PKU-based memory isolation systems*, https://dl.acm.org/doi/10.5555/3489212.3489292
* [2] Oldani et al, CCSW'24: *Binsweep: Reliably Restricting Untrusted Instruction Streams with Static Binary Analysis and Control-Flow Integrity*, https://dl.acm.org/doi/10.1145/3689938.3694778)
* [3] Neugschwandtner et al, EuroSec'26: *HypoVisor: Multi-Tenant POSIX Process Virtualization in Userspace for Untrusted Native Code*, https://dl.acm.org/doi/10.1145/3803525.3804989
