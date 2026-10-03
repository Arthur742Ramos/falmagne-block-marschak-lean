from pathlib import Path
root = Path(__file__).resolve().parent.parent
modules = ['Basic', 'Mobius', 'Representation', 'Path', 'Flow', 'Conservation', 'PathChoice', 'ChoiceMobius', 'Falmagne']
parts = ["/-\nFalmagne–Block–Marschak characterization.\nAuthors: Arthur Freitas Ramos, David Barros Hulak,\nRuy Jose Guerra Barretto de Queiroz.\nReleased under Apache 2.0.\n-/\nmodule\npublic import Mathlib.Data.Finsupp.Basic\npublic import Mathlib.Data.Finsupp.Defs\npublic import Mathlib.Data.List.NodupEquivFin\npublic import Mathlib.Data.Finset.Max\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Basic\npublic import Mathlib.Basic.Real.Basic\npublic import Mathlib.Data.Finset.Interval\npublic import Mathlib.Data.Nat.Choose.Sum\npublic import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Basic\npublic import Mathlib.Tactic\n\n@[expose] public section\n\n"]
for name in modules:
    text = (root / 'EconomicsNextProof' / f'{name}.lean').read_text()
    text = '\n'.join(line for line in text.splitlines() if not (line.startswith('import ') or line.startswith('public import ') or line == 'module' or line == '@[expose] public section'))
    parts.append(f'\n/-! ## {name} -/\n{text}\n')
(root / 'Solution.lean').write_text(''.join(parts))
basic = (root / 'EconomicsNextProof/Basic.lean').read_text()
start = basic.index('namespace Falmagne')
end = basic.index('variable {l : List X}')
challenge = 'module\npublic import Mathlib.Data.Finsupp.Basic\npublic import Mathlib.Data.Finsupp.Defs\npublic import Mathlib.Data.List.NodupEquivFin\npublic import Mathlib.Data.Finset.Max\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Basic\npublic import Mathlib.Basic.Real.Basic\npublic import Mathlib.Data.Finset.Interval\npublic import Mathlib.Data.Nat.Choose.Sum\npublic import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra\npublic import Mathlib.LinearAlgebra.FiniteDimensional.Basic\npublic import Mathlib.Tactic\n\n@[expose] public section\n\n/-! The independent full finite random-utility challenge. -/\n'
challenge += basic[start:end] + '\nend Falmagne\n\n'
mobius = (root / 'EconomicsNextProof/Mobius.lean').read_text()
start = mobius.index('namespace EconomicsNextProof')
end = mobius.index('omit [Fintype X]')
challenge += mobius[start:end] + '\nend EconomicsNextProof\n\n'
challenge += '''namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def blockMarschak (p : Finset X → X → ℝ) (x : X) (A : Finset X) : ℝ :=
  EconomicsNextProof.upperMobius (fun B => p B x) A

variable [Nonempty X]
def BlockMarschakNonnegative (p : Finset X → X → ℝ) : Prop :=
  ∀ x A, x ∈ A → 0 ≤ blockMarschak p x A

def RandomUtilityRepresentable (p : Finset X → X → ℝ) : Prop :=
  ∃ w : RankingLaw X, IsRankingLaw w ∧ Represents w p

/-- Full Falmagne–Block–Marschak equivalence, with no cardinality bound. -/
theorem falmagne_blockMarschak {p : Finset X → X → ℝ} (hp : IsChoiceRule p) :
    RandomUtilityRepresentable p ↔ BlockMarschakNonnegative p := by
  sorry

end Falmagne
'''
(root / 'Challenge.lean').write_text(challenge)
