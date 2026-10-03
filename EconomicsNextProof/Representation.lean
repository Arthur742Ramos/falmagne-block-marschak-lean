module

public import EconomicsNextProof.Basic

@[expose] public section

namespace Falmagne

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

/-- Unit flow through the lower-contour edge of a strict ranking. -/
noncomputable def rankingEdge (l : List X) (x : X) (A : Finset X) : ℝ :=
  if x ∈ A ∧ A = lowerContour l x then 1 else 0

lemma rankingEdge_nonneg (l : List X) (x : X) (A : Finset X) :
    0 ≤ rankingEdge l x A := by
  unfold rankingEdge
  split <;> norm_num

@[simp] lemma rankingEdge_eq_zero_of_not_mem (hx : x ∉ A) :
    rankingEdge l x A = 0 := by simp [rankingEdge, hx]

/-- Marginal lower-contour flow of a finitely supported ranking law. -/
noncomputable def lawFlow (w : RankingLaw X) (x : X) (A : Finset X) : ℝ :=
  w.sum (fun l a => a * rankingEdge l x A)

lemma lawFlow_nonneg {w : RankingLaw X} (hw : ∀ l, 0 ≤ w l) (x : X) (A : Finset X) :
    0 ≤ lawFlow w x A := by
  unfold lawFlow Finsupp.sum
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (rankingEdge_nonneg l x A)

lemma lawFlow_off_menu (w : RankingLaw X) (hx : x ∉ A) :
    lawFlow w x A = 0 := by
  simp [lawFlow, rankingEdge, hx]

/-- A ranking law always generates a normalized stochastic choice rule. -/
lemma represented_isChoiceRule {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) : IsChoiceRule p := by
  unfold Represents at hp
  refine ⟨?_, ?_, ?_⟩
  · intro A x
    rw [hp A x]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hw.1 l) (rankingChoice_nonneg l A x)
  · intro A x hx
    rw [hp A x]
    simp [rankingChoice, hx]
  · intro A hA
    simp_rw [hp]
    unfold Finsupp.sum
    rw [Finset.sum_comm]
    calc
      _ = ∑ l ∈ w.support, w l * (∑ x ∈ A, rankingChoice l A x) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
      _ = ∑ l ∈ w.support, w l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [sum_rankingChoice (hw.2.1 l hl) hA, mul_one]
      _ = 1 := hw.2.2

end Falmagne
