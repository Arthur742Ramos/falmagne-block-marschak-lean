# Independent mathematical and implementation review

Review date: 2026-10-03 (UTC)

## Verdict

The source statement, modular development, and standalone Challenge/Solution preserve the full finite Falmagne–Block–Marschak characterization. No mathematical correction remains. The review was AI-assisted and separate from proof-library authorship; it is not a claim of human peer review or registry acceptance.

## Mathematical scope

- The alternative type is an arbitrary finite nonempty type, with no fixed cardinality or cardinality bound.
- All nonempty menus are observed. Choice probabilities are nonnegative, zero off-menu, and normalized on each nonempty menu.
- Block–Marschak sums include the original menu and all its supersets, with the standard alternating sign.
- The conclusion constructs a single nonnegative mass-one law on complete duplicate-free best-to-worst lists. These lists encode strict linear rankings; the choice predicate picks the earliest element present in the menu.
- Neither a ranking law nor a flow decomposition is assumed in the economic theorem.
- The theorem is the strict-ranking/no-ties random-utility characterization. It does not assert a theorem about arbitrary menu-dependent tie breaking.
- Singleton alternatives are included. Empty-menu zero is harmless explicit bookkeeping.
- The locally proved decomposition eliminates alternatives best-first from the full set to the empty set. Its path edges agree with exact lower-contour sets, so its direction is consistent with the ranking semantics.

## Proof and packaging checks

The complete mathematical proof was read, including Boolean Möbius inversion, conservation, positive path construction, minimum-edge subtraction, induction on positive-edge count, and reconstruction of all menu probabilities.

Challenge.lean contains only Mathlib imports, substantive definitions, and its single deliberate target theorem hole. It does not import Solution or the development library. Solution.lean contains the flattened genuine proof and imports only Mathlib. Its source contains no sorry, admit, axiom, or unsafe declarations.

The comparator configuration checks the target theorem and all eleven target-relevant definitions, including RankingLaw and each economic predicate. upperSum is a proof helper rather than part of the target statement.

Independent imports were successfully checked under Lean 4.35.0-rc2 (compiler commit 11acb17ec6b07a8f9e9173e6845197929540936b) and mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55. Both the modular theorem and standalone theorem printed the expected arbitrary-type statement. The standalone theorem, its sufficiency proof, and flow_decomposition depend only on propext, Classical.choice, and Quot.sound. See independent-axioms-rc2.log.

Metadata was checked against pinned Palomar package requirements. It records the classical source-based origin, human authors and responsible maintainer, actual AI assistance, honest scope, and standard axioms. Empty MSC classification is expressly accepted by the pinned authoritative CONTRIBUTING requirements, despite a stricter comment in its example template. Classification econ.TH and math.CO is substantively appropriate.

These checks are local Lean kernel/source audits. They do not establish a passing Comparator/NanoDa run or the official hosted standard execution profile. Those gates were unresolved when this review was recorded.

## Source fidelity and prior art

The statement was reconciled with Fiorini (2004), A short proof of a theorem of Falmagne, DOI https://doi.org/10.1016/j.jmp.2003.11.003, and the accessible primary exposition in Doignon–Saito (2023), section 3, equations 13–21 and the preceding acyclic flow decomposition theorem: https://saito.caltech.edu/documents/29716/Adjacencies_arxiv.pdf.

The bounded prior-art search examined public Lean searches, the Econlib glossary, and all 646 Lean source/example/test files in Econlib commit 003655ccf010cdf44c4f67d6675167b54ce0e9df. No corresponding named Falmagne/Block–Marschak random-utility characterization was found. Existing Boolean Möbius inversion is acknowledged as infrastructure. This supports only that bounded repository-search conclusion, not a worldwide first-formalization claim.
