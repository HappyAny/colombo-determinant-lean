# Development context and verification boundary

This note concerns the reported original session, not a controlled model evaluation.

| Item | Record |
| --- | --- |
| Model | GPT-6 Astra, as reported by the user |
| Reasoning effort | max |
| Harness | Codex only |
| Fast mode | Disabled |
| Special orchestration skills | None used during the original solution and formalization |
| User-written prompts | Brief requests for an offline solution, Lean formalization, and a complete single-file proof |
| Duration | Approximately 50 minutes, as reported by the user |
| Online search | Explicitly prohibited during the original mathematical solution and Lean formalization |
| Original checking environment | Pre-existing Lean 4.32.0 and mathlib v4.32.0 installation |

The brief prompts described the task and requested the proof artifact. They did not
supply a detailed mathematical strategy. This observation concerns the user's task
prompts; Codex's ordinary system instructions and tools remained in use.

The original verification record shows successful compilation of the standalone
source and the final theorem's axiom list. The publication copy retains the same
SHA-256 and is checked again against the same cached toolchain and libraries.
The mathematical statement checked by Lean is independent of the accuracy of the
session-timing and bibliographical descriptions.

The related papers and repositories were consulted after the original proof and
formalization, for comparison and manuscript writing. Those later activities and
GitHub publication are excluded from the reported 50-minute duration.

## Knowledge coverage is unknown

The scope of Astra's training data and prior knowledge is unknown to the participants,
including possible exposure to related mathematics or texts. An explicit prohibition
on online search constrains the session's actions; it cannot establish absence of
prior exposure in training. The workflow and efficiency observations are consequently
**for reference only**. No exact knowledge cutoff, model-level originality guarantee,
or controlled performance advantage is asserted.

## An open question about additional orchestration

As a model improves, it may carry out more planning, tool selection, and error
correction internally. This suggests a hypothesis: for some bounded tasks, the
marginal gain from additional task-specific orchestration might decrease.

This session cannot establish such a trend. Codex still supplied an execution and
context environment, and Lean provided a separate proof checker. A useful study
would compare several models and harnesses on the same tasks with matched resource
budgets and repeated runs, measuring verified completion, cost, and failure modes.

This is a question motivated by a case report, not a conclusion that harnesses or
formal verification have become unnecessary.
