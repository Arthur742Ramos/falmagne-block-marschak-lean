module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

/-! Boolean upper Möbius inversion, for arbitrary finite ground sets. -/
@[expose] public section

namespace EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def upperSum (f : Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset X => A ⊆ B), f B

noncomputable def upperMobius (f : Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset X => A ⊆ B),
    (-1 : ℝ) ^ (B \ A).card * f B

omit [Fintype X] in
private lemma alternating_powerset (s : Finset X) :
    (∑ D ∈ s.powerset, (-1 : ℝ) ^ D.card) = if s = ∅ then 1 else 0 := by
  exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := s))

lemma alternating_interval (A C : Finset X) (hAC : A ⊆ C) :
    (∑ B ∈ Finset.Icc A C, (-1 : ℝ) ^ (B \ A).card) = if A = C then 1 else 0 := by
  rw [Finset.Icc_eq_image_powerset hAC, Finset.sum_image]
  · have h : ∀ D ∈ (C \ A).powerset, (A ∪ D) \ A = D := by
      intro D hD
      have hDA := Finset.mem_powerset.mp hD
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · tauto
      · intro hx
        exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hDA hx)).2⟩
    calc
      ∑ D ∈ (C \ A).powerset, (-1 : ℝ) ^ ((A ∪ D) \ A).card
          = ∑ D ∈ (C \ A).powerset, (-1 : ℝ) ^ D.card := by
              exact Finset.sum_congr rfl (fun D hD => by rw [h D hD])
      _ = if A = C then 1 else 0 := by
        rw [alternating_powerset]
        congr 1
        exact propext ⟨fun h => Finset.Subset.antisymm hAC
          (Finset.sdiff_eq_empty_iff_subset.mp h), fun h => by simp [h]⟩

  · intro D hD E hE hEq
    have hDA := Finset.mem_powerset.mp hD
    have hEA := Finset.mem_powerset.mp hE
    ext x
    have hdx : x ∈ D → x ∉ A := fun hx => (Finset.mem_sdiff.mp (hDA hx)).2
    have hex : x ∈ E → x ∉ A := fun hx => (Finset.mem_sdiff.mp (hEA hx)).2
    have heq := Finset.ext_iff.mp hEq x
    simp only [Finset.mem_union] at heq
    tauto

private noncomputable def booleanMu : IncidenceAlgebra ℝ (Finset X) where
  toFun A B := if A ⊆ B then (-1 : ℝ) ^ (B \ A).card else 0
  eq_zero_of_not_le' := by intros; simp_all

private lemma booleanMu_eq_mu :
    (booleanMu : IncidenceAlgebra ℝ (Finset X)) = IncidenceAlgebra.mu ℝ := by
  have h : (booleanMu : IncidenceAlgebra ℝ (Finset X)) *
      IncidenceAlgebra.zeta ℝ = 1 := by
    apply IncidenceAlgebra.ext
    intro A C hAC
    rw [IncidenceAlgebra.mul_apply]
    calc
      ∑ B ∈ Finset.Icc A C, booleanMu A B * IncidenceAlgebra.zeta ℝ B C
          = ∑ B ∈ Finset.Icc A C, (-1 : ℝ) ^ (B \ A).card := by
              apply Finset.sum_congr rfl
              intro B hB
              have hb := Finset.mem_Icc.mp hB
              simp [booleanMu, IncidenceAlgebra.zeta_apply, hb.1, hb.2]
      _ = (1 : IncidenceAlgebra ℝ (Finset X)) A C := by
        rw [alternating_interval A C hAC, IncidenceAlgebra.one_apply]
  calc
    booleanMu = booleanMu * (IncidenceAlgebra.zeta ℝ * IncidenceAlgebra.mu ℝ) := by
      rw [IncidenceAlgebra.zeta_mul_mu, mul_one]
    _ = (booleanMu * IncidenceAlgebra.zeta ℝ) * IncidenceAlgebra.mu ℝ := by rw [mul_assoc]
    _ = IncidenceAlgebra.mu ℝ := by rw [h, one_mul]

private lemma upperSum_eq_Ici (f : Finset X → ℝ) (A : Finset X) :
    upperSum f A = ∑ B ∈ Finset.Ici A, f B := by
  unfold upperSum
  congr 1
  ext B
  simp

private lemma upperMobius_eq_mu (f : Finset X → ℝ) (A : Finset X) :
    upperMobius f A = ∑ B ∈ Finset.Ici A, IncidenceAlgebra.mu ℝ A B * f B := by
  have hs : Finset.univ.filter (fun B : Finset X => A ⊆ B) = Finset.Ici A := by
    ext B
    simp
  rw [upperMobius, hs]
  apply Finset.sum_congr rfl
  intro B hB
  rw [← booleanMu_eq_mu]
  simp [booleanMu, Finset.mem_Ici.mp hB]

/-- Möbius inversion of the upper subset sum on the Boolean lattice. -/
theorem upperMobius_upperSum (f : Finset X → ℝ) : upperMobius (upperSum f) = f := by
  funext A
  rw [upperMobius_eq_mu]
  exact (IncidenceAlgebra.moebius_inversion_top f (upperSum f)
    (fun B => upperSum_eq_Ici f B) A).symm

private noncomputable def upperSumLinear :
    (Finset X → ℝ) →ₗ[ℝ] (Finset X → ℝ) where
  toFun := upperSum
  map_add' f g := by
    funext A
    simp [upperSum, Finset.sum_add_distrib]
  map_smul' r f := by
    funext A
    simp [upperSum, Finset.mul_sum]

/-- The upper subset sum and its Möbius transform are two-sided inverses. -/
theorem upperSum_upperMobius (f : Finset X → ℝ) : upperSum (upperMobius f) = f := by
  have hinj : Function.Injective (upperSumLinear (X := X)) := by
    intro f g hfg
    have h := congrArg upperMobius hfg
    simpa only [upperSumLinear, LinearMap.coe_mk, AddHom.coe_mk,
      upperMobius_upperSum] using h
  have hsurj := (LinearMap.injective_iff_surjective.mp hinj)
  obtain ⟨g, hg⟩ := hsurj f
  change upperSum g = f at hg
  rw [← hg, upperMobius_upperSum]

/-- A constant upper Möbius transform is supported only at the full set. -/
theorem upperMobius_const (c : ℝ) (A : Finset X) :
    upperMobius (fun _ => c) A = if A = Finset.univ then c else 0 := by
  have hs : Finset.univ.filter (fun B : Finset X => A ⊆ B) =
      Finset.Icc A Finset.univ := by
    ext B
    simp
  rw [upperMobius, hs, ← Finset.sum_mul,
    alternating_interval A Finset.univ (Finset.subset_univ A)]
  split_ifs <;> simp

end EconomicsNextProof



