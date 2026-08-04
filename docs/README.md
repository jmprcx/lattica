# Lattica documentation

This index is the canonical map of the repository documentation. Documents are grouped by authority so that current requirements are not confused with research notes or historical audit snapshots.

## Current project guides

- [External audit handoff](AUDITORS.md) — reviewed surface, trust model, reproduction, and exclusions.
- [Audit-readiness status](audit-readiness-status.md) — frozen baseline and current development posture.
- [Remediation status](remediation-status.md) — disposition of implementation findings.
- [Production parameters](parameters.md) — selected cryptographic parameters.
- [Wire format](wire-format.md) — normative prover/node byte encodings.
- [Protocol v1 decisions](protocol-v1-decisions.md) — resolved protocol-level design choices.
- [Post-quantum zero-knowledge stack](../POST_QUANTUM_ZERO_KNOWLEDGE_STACK.md) — explanatory cryptographic overview.

## Protocol and implementation assurance

- [Plonky3 audit scope](audit-scope-p3.md)
- [Join-split constraint audit](joinsplit-constraint-audit.md)
- [HTLC constraint audit](htlc-constraint-audit.md)
- [Batch constraint audit](batch-constraint-audit.md)
- [Soundness budget](soundness-budget.md)
- [Hash-function analysis](hash-function-analysis.md)
- [Implementation audit](lattica-implementation-audit.md)
- [Full-node integration requirements](full-node-security-integration.md)

## Architecture and roadmap

- [Framework decision](framework-decision.md)
- [Block-production and incentive design](block-production-consensus.md)
- [Multi-asset, exchange, and issuance architecture](multi-asset-exchanges-issuance-cto.md)
- [GPU proving](gpu-acceleration.md)
- [Recursive aggregation status](recursion-aggregation-status.md)
- [Recursive aggregation parameters](recursion-aggregation-params.md)
- [Recursion design](recursion-design.md)
- [Recursive verifier audit](recursion-verifier-audit.md)

## Frozen and historical records

These documents preserve the claims and evidence associated with a particular development stage. Their dates and commit references are part of the record; consult the current guides above before applying them to the working tree.

- [v3 audit handoff](v3-audit-handoff.md)
- [v3 batch audit handoff](v3-batch-audit-handoff.md)
- [v3 external audit report](v3-external-audit-report.md)
- [v3 internal audit rounds](v3-internal-audit.md), [round 2](v3-internal-audit-round2.md), and [round 3](v3-internal-audit-round3.md)
- [v3 batch internal audit](v3-batch-internal-audit.md)
- [Original transaction-stack audit](transaction-stack-audit.md)
- [Earlier audit scope](audit-scope.md)
- [Earlier production-readiness assessment](production-readiness.md)
- [Earlier general soundness analysis](soundness.md)
- [Plonky3 port plan](plonky3-port-plan.md)

## Authority rules

When documents disagree:

1. `SPEC.md` and `wire-format.md` control protocol and encoding requirements.
2. `AUDITORS.md`, `audit-scope-p3.md`, and `audit-readiness-status.md` control current audit claims.
3. Circuit-specific audits control their named constraint surfaces.
4. Research status documents describe experimental code only.
5. Dated audit reports remain evidence for their recorded revision and do not automatically describe later working-tree changes.
