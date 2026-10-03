module

public import EconomicsNextProof.Representation
public import EconomicsNextProof.Mobius

@[expose] public section

namespace Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

lemma upperSum_rankingEdge (hl : IsRanking l) (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (rankingEdge l x) A = rankingChoice l A x := by
  by_cases hA : A ⊆ lowerContour l x
  · unfold upperSum
    rw [Finset.sum_eq_single (lowerContour l x)]
    · simp [rankingEdge, self_mem_lowerContour hl x, rankingChoice, hA, hx]
    · intro B hB hne
      simp [rankingEdge, hne]
    · intro hn
      exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)).elim
  · have hz : upperSum (rankingEdge l x) A = 0 := by
      unfold upperSum
      apply Finset.sum_eq_zero
      intro B hB
      have hne : B ≠ lowerContour l x := by
        intro h
        exact hA (h ▸ (Finset.mem_filter.mp hB).2)
      simp [rankingEdge, hne]
    rw [hz]
    simp [rankingChoice, hA]

lemma upperSum_lawFlow (w : RankingLaw X) (hw : ∀ l ∈ w.support, IsRanking l)
    (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (lawFlow w x) A = w.sum (fun l a => a * rankingChoice l A x) := by
  unfold upperSum lawFlow Finsupp.sum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.mul_sum]
  congr 1
  exact upperSum_rankingEdge (hw l hl) x A hx

/-- The Möbius coefficient equals the probability of the exact lower contour. -/
theorem mobius_eq_lawFlow {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : ∀ l ∈ w.support, IsRanking l) (hp : Represents w p) (x : X) (A : Finset X)
    (hx : x ∈ A) :
    upperMobius (fun B => p B x) A = lawFlow w x A := by
  calc
    _ = upperMobius (upperSum (lawFlow w x)) A := by
      unfold upperMobius
      apply Finset.sum_congr rfl
      intro B hB
      have hAB : A ⊆ B := (Finset.mem_filter.mp hB).2
      rw [upperSum_lawFlow w hw x B (hAB hx)]
      change _ * p B x = _
      rw [hp B x]
    _ = lawFlow w x A := congrFun (upperMobius_upperSum (lawFlow w x)) A

/-- Every random-ranking choice rule satisfies all Block–Marschak inequalities. -/
theorem blockMarschak_necessary {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) :
    ∀ x A, x ∈ A → 0 ≤ upperMobius (fun B => p B x) A := by
  intro x A hx
  rw [mobius_eq_lawFlow hw.2.1 hp x A hx]
  exact lawFlow_nonneg hw.1 x A

end Falmagne
