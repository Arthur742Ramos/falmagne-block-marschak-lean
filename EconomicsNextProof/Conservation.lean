module

public import EconomicsNextProof.Basic
public import EconomicsNextProof.Mobius
public import EconomicsNextProof.Path

@[expose] public section

namespace Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Block–Marschak transform of a finite choice rule. -/
noncomputable def blockMarschak (p : Finset X → X → ℝ) (x : X) (A : Finset X) : ℝ :=
  upperMobius (fun B => p B x) A

lemma blockMarschak_not_mem (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (x : X) (hx : x ∉ A) :
    blockMarschak p x A = -blockMarschak p x (insert x A) := by
  classical
  let S := univ.filter (fun B : Finset X => A ⊆ B)
  let T := univ.filter (fun B : Finset X => insert x A ⊆ B)
  have hTS : T ⊆ S := by
    intro B hB
    simp only [T, S, mem_filter, mem_univ, true_and] at hB ⊢
    exact (subset_insert x A).trans hB
  have hrestrict : (∑ B ∈ S, (-1 : ℝ) ^ (B \ A).card * p B x) =
      ∑ B ∈ T, (-1 : ℝ) ^ (B \ A).card * p B x := by
    symm
    apply sum_subset hTS
    intro B hBS hBT
    have hxB : x ∉ B := by
      intro hxB
      apply hBT
      simp only [T, mem_filter, mem_univ, true_and]
      exact insert_subset hxB ((mem_filter.mp hBS).2)
    simp [hp.2.1 B x hxB]
  change (∑ B ∈ S, (-1 : ℝ) ^ (B \ A).card * p B x) =
    -(∑ B ∈ T, (-1 : ℝ) ^ (B \ insert x A).card * p B x)
  rw [hrestrict, ← sum_neg_distrib]
  apply sum_congr rfl
  intro B hBT
  have hxB : x ∈ B := (mem_filter.mp hBT).2 (mem_insert_self x A)
  have hd : B \ A = insert x (B \ insert x A) := by
    ext y
    simp only [mem_sdiff, mem_insert]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hy.1, by simpa [hyx] using hy.2⟩
    · intro hy
      rcases hy with rfl | hy
      · exact ⟨hxB, hx⟩
      · exact ⟨hy.1, fun hyA => hy.2 (Or.inr hyA)⟩
  have hnot : x ∉ B \ insert x A := by simp
  rw [hd, card_insert_of_notMem hnot, pow_succ]
  ring

lemma blockMarschak_univ (p : Finset X → X → ℝ) (x : X) :
    blockMarschak p x univ = p univ x := by
  have hfilter : univ.filter (fun B : Finset X => univ ⊆ B) = {univ} := by
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => Subset.antisymm (subset_univ B) h, fun h => by simp [h]⟩
  unfold blockMarschak upperMobius
  rw [hfilter]
  simp

lemma blockMarschak_source [Nonempty X] (p : Finset X → X → ℝ)
    (hp : IsChoiceRule p) : ∑ x : X, blockMarschak p x univ = 1 := by
  simp_rw [blockMarschak_univ]
  exact hp.2.2 univ univ_nonempty

/-- Normalization turns the total Möbius mass into a full-set point mass. -/
lemma blockMarschak_total (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) :
    ∑ x : X, blockMarschak p x A = if A = univ then 1 else 0 := by
  have hnorm (B : Finset X) (hAB : A ⊆ B) : (∑ x : X, p B x) = 1 := by
    calc
      (∑ x : X, p B x) = ∑ x ∈ B, p B x := by
        symm
        exact sum_subset (subset_univ B) (fun x _ hx => hp.2.1 B x hx)
      _ = 1 := hp.2.2 B (hA.mono hAB)
  unfold blockMarschak upperMobius
  rw [sum_comm]
  calc
    (∑ B ∈ univ.filter (fun B : Finset X => A ⊆ B),
        ∑ x : X, (-1 : ℝ) ^ (B \ A).card * p B x) =
      ∑ B ∈ univ.filter (fun B : Finset X => A ⊆ B),
        (-1 : ℝ) ^ (B \ A).card * 1 := by
      apply sum_congr rfl
      intro B hB
      rw [← mul_sum, hnorm B (mem_filter.mp hB).2]
    _ = if A = univ then 1 else 0 := upperMobius_const 1 A

lemma blockMarschak_conserve (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) (hproper : A ≠ univ) :
    (∑ x ∈ A, blockMarschak p x A) =
      ∑ x ∈ univ \ A, blockMarschak p x (insert x A) := by
  have htotal := blockMarschak_total p hp A hA
  rw [ite_eq_right hproper] at htotal
  have hoff : (∑ x ∈ univ \ A, blockMarschak p x A) =
      -(∑ x ∈ univ \ A, blockMarschak p x (insert x A)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro x hx
    exact blockMarschak_not_mem p hp A x (mem_sdiff.mp hx).2
  have hsplit := sum_sdiff (subset_univ A) (f := fun x => blockMarschak p x A)
  rw [hoff, htotal] at hsplit
  linarith

/-- Nonnegative Block–Marschak coefficients form a unit Boolean-lattice flow. -/
theorem blockMarschak_isFlow [Nonempty X] (p : Finset X → X → ℝ)
    (hp : IsChoiceRule p)
    (hBM : ∀ x A, x ∈ A → 0 ≤ blockMarschak p x A) :
    IsFlow (blockMarschak p) 1 := by
  constructor
  · exact hBM
  · exact blockMarschak_source p hp
  · exact blockMarschak_conserve p hp

end Falmagne
