## 🐟 PERCH: Proving Execution Restrictions and Control-flow Hardening

The goal of this project is to formally verify software-enforced privilege levels.
Using binary verifiers such as Binsweep [2] that analyze a binary before it is run, we can check that it only contains instructions from an allow-list, and thus enforce that a program does not access certain resources.
Possible use cases include lightweight sandboxing such as HypoVisor [3].

However, on architectures with variable instruction lengths, programs that jump into the middle of an instruction could start executing instructions that were never intended to be executed, so it is important to enforce control-flow integrity, in particular, for indirect jumps. 
Intel processors offer CET (Control-flow enforcement technology), which consists of IBT (indirect branch tracking) and SHSTK (shadow stack). However, currently, Linux supports SHSTK only in user mode and IBT only in kernel mode, and ensuring that these features are indeed enabled in all deployments is challenging in practice. Therefore, Binsweep [2] enforces a CFI policy that does not rely on these features being enabled. It only uses the `ENDBR` instruction that was introduced as part of CET, but still works if CET is disabled (in that case, `ENDBR` is simply treated as a `NOP`). To use Binsweep, one has to use a special compiler phase (TODO insert links to the Graal CFI phase and LLVM CFI phase) that replaces all `RET` instructions by indirect forward jumps, and adds a pattern around each indirect forward jump that checks, before jumping, whether the target of the jump is an `ENDBR` instruction. Before running a program, a binary verifier can then check if the binary indeed contains the required pattern around each forward jump, by analyzing the instruction stream starting after each `ENDBR` instruction.

For protecting memory regions, features like memory-protection keys (MPK) can be used, as long as one makes sure that the program to be isolated does not run any `WRPKRU` instruction (which modifies the protection registers).

It is very tricky to get all the details right, as described in the "PKU pitfalls" paper [1].
Therefore, we want to write machine-checked proofs that the policies implemented by binary verifiers indeed achieve the desired guarantees.


### Build

It is recommended to browse and edit the files using VS Code. The [Lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) can install the right Lean version (as given in `./lean-toolchain`) as well as the dependencies (currently just the [Kraken x86 semantics](https://github.com/AeneasVerif/kraken)).

`lake` is Lean's build tool, and `elan` is used to manage different Lean versions. Both of these can be installed from within the VS Code Lean extension.

To build the project, run `lake build`.


### References

* [1] Connor et. al, SEC'20: *PKU pitfalls: attacks on PKU-based memory isolation systems*, https://dl.acm.org/doi/10.5555/3489212.3489292
* [2] Oldani et al, CCSW'24: *Binsweep: Reliably Restricting Untrusted Instruction Streams with Static Binary Analysis and Control-Flow Integrity*, https://dl.acm.org/doi/10.1145/3689938.3694778)
* [3] Neugschwandtner et al, EuroSec'26: *HypoVisor: Multi-Tenant POSIX Process Virtualization in Userspace for Untrusted Native Code*, https://dl.acm.org/doi/10.1145/3803525.3804989
