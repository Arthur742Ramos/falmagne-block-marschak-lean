module

public import EconomicsNextProof.ChoiceMobius
public import EconomicsNextProof.Conservation
public import EconomicsNextProof.PathChoice
public import EconomicsNextProof.Flow

/-!
# Falmagne–Block–Marschak random-utility characterization

The alternative type is any finite nonempty type. A single probability distribution
on complete strict rankings reproduces every nonempty-menu choice exactly if all
Block–Marschak coefficients are nonnegative. The sufficiency proof constructs the
ranking law from the nonnegative Boolean-lattice flow. No decomposition hypothesis
is part of the economic statement.

Primary references:
* Falmagne (1978), A representation theorem for finite random scale systems.
* Fiorini (2004), A short proof of a theorem of Falmagne.
* Doignon and Saito (2023), Adjacencies on random ordering polytopes and flow polytopes.
-/
@[expose] public section

namespace Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- The exact observed probabilities satisfy all Block–Marschak inequalities. -/
def BlockMarschakNonnegative (p : Finset X → X → ℝ) : Prop :=
  ∀ x A, x ∈ A → 0 ≤ blockMarschak p x A

/-- Stochastic rationalizability by a single menu-independent strict-ranking law. -/
def RandomUtilityRepresentable (p : Finset X → X → ℝ) : Prop :=
  ∃ w : RankingLaw X, IsRankingLaw w ∧ Represents w p

lemma randomUtility_necessary {p : Finset X → X → ℝ}
    (h : RandomUtilityRepresentable p) : BlockMarschakNonnegative p := by
  obtain ⟨w, hw, hp⟩ := h
  exact blockMarschak_necessary hw hp

/-- Construct a common ranking law from the nonnegative Block–Marschak flow. -/
lemma randomUtility_sufficient {p : Finset X → X → ℝ}
    (hp : IsChoiceRule p) (hBM : BlockMarschakNonnegative p) :
    RandomUtilityRepresentable p := by
  obtain ⟨w, hnonneg, hrank, hmass, hflow⟩ :=
    flow_decomposition (blockMarschak_isFlow p hp hBM)
  refine ⟨w, ⟨hnonneg, hrank, hmass⟩, ?_⟩
  intro A x
  by_cases hx : x ∈ A
  · have hwflow : ∀ B, x ∈ B → lawFlow w x B = blockMarschak p x B := by
      intro B hxB
      calc
        lawFlow w x B = w.sum (fun l a => a * pathFlow l x B) := by
          unfold lawFlow Finsupp.sum
          apply Finset.sum_congr rfl
          intro l hl
          change w l * rankingEdge l x B = w l * pathFlow l x B
          rw [pathFlow_eq_rankingEdge (hrank l hl)]
        _ = blockMarschak p x B := hflow x B hxB
    calc
      p A x = upperSum (blockMarschak p x) A := by
        exact (congrFun (upperSum_upperMobius (fun B => p B x)) A).symm
      _ = upperSum (lawFlow w x) A := by
        unfold upperSum
        apply Finset.sum_congr rfl
        intro B hB
        exact (hwflow B ((Finset.mem_filter.mp hB).2 hx)).symm
      _ = w.sum (fun l a => a * rankingChoice l A x) :=
        upperSum_lawFlow w hrank x A hx
  · rw [hp.2.1 A x hx]
    simp [rankingChoice, hx]

/-- Full Falmagne–Block–Marschak equivalence on an arbitrary finite alternative set. -/
theorem falmagne_blockMarschak {p : Finset X → X → ℝ} (hp : IsChoiceRule p) :
    RandomUtilityRepresentable p ↔ BlockMarschakNonnegative p :=
  ⟨randomUtility_necessary, randomUtility_sufficient hp⟩

end Falmagne
