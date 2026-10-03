module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def outflow (q : X → Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ x ∈ A, q x A
noncomputable def inflow (q : X → Finset X → ℝ) (A : Finset X) : ℝ :=
  ∑ y ∈ Finset.univ \ A, q y (insert y A)

structure IsFlow (q : X → Finset X → ℝ) (m : ℝ) : Prop where
  nonneg : ∀ x A, x ∈ A → 0 ≤ q x A
  source : outflow q Finset.univ = m
  conserve : ∀ A, A.Nonempty → A ≠ Finset.univ → outflow q A = inflow q A

noncomputable def unitEdge (y : X) (B : Finset X) (x : X) (A : Finset X) : ℝ :=
  if x = y ∧ A = B then 1 else 0

noncomputable def pathFlow : List X → X → Finset X → ℝ
  | [], _, _ => 0
  | y :: l, x, A => unitEdge y (y :: l).toFinset x A + pathFlow l x A

@[simp] lemma pathFlow_nil (x : X) (A : Finset X) : pathFlow [] x A = 0 := rfl
@[simp] lemma pathFlow_cons (y : X) (l : List X) (x : X) (A : Finset X) :
    pathFlow (y :: l) x A = unitEdge y (y :: l).toFinset x A + pathFlow l x A := rfl

lemma outflow_add (q r : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => q x B + r x B) A = outflow q A + outflow r A := by
  simp [outflow, Finset.sum_add_distrib]
lemma inflow_add (q r : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => q x B + r x B) A = inflow q A + inflow r A := by
  simp [inflow, Finset.sum_add_distrib]
lemma outflow_sub (q r : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => q x B - r x B) A = outflow q A - outflow r A := by
  simp [outflow, Finset.sum_sub_distrib]
lemma inflow_sub (q r : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => q x B - r x B) A = inflow q A - inflow r A := by
  simp [inflow, Finset.sum_sub_distrib]
lemma outflow_mul (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    outflow (fun x B => a * q x B) A = a * outflow q A := by
  simp [outflow, Finset.mul_sum]
lemma inflow_mul (a : ℝ) (q : X → Finset X → ℝ) (A : Finset X) :
    inflow (fun x B => a * q x B) A = a * inflow q A := by
  unfold inflow
  rw [Finset.mul_sum]

lemma outflow_unitEdge (hy : y ∈ B) (A : Finset X) :
    outflow (unitEdge y B) A = if A = B then 1 else 0 := by
  classical
  by_cases h : A = B
  · subst A
    simp [outflow, unitEdge, hy]
  · simp [outflow, unitEdge, h]

lemma inflow_unitEdge (hy : y ∈ B) (A : Finset X) :
    inflow (unitEdge y B) A = if A = B.erase y then 1 else 0 := by
  classical
  by_cases h : A = B.erase y
  · subst A
    have hy' : y ∈ Finset.univ \ B.erase y := by simp
    have hi : insert y (B.erase y) = B := Finset.insert_erase hy
    unfold inflow
    rw [Finset.sum_eq_single y]
    · simp [unitEdge, hi]
    · intro z hz hzy
      simp [unitEdge, hzy]
    · intro hy0
      exact (hy0 hy').elim
  · have hzero : ∀ z ∈ Finset.univ \ A, unitEdge y B z (insert z A) = 0 := by
      intro z hz
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
      unfold unitEdge
      split_ifs with heq
      · have hz' : z = y := heq.1
        subst z
        have : A = B.erase y := by rw [← heq.2]; simp [hz]
        exact (h this).elim
      · rfl
    simp [inflow, Finset.sum_eq_zero hzero, h]

lemma pathFlow_nonneg (l : List X) (x : X) (A : Finset X) :
    0 ≤ pathFlow l x A := by
  induction l with
  | nil => simp
  | cons y l ih =>
      rw [pathFlow_cons]
      have h : 0 ≤ unitEdge y (y :: l).toFinset x A := by unfold unitEdge; split <;> norm_num
      exact add_nonneg h ih

lemma pathFlow_zero_of_not_mem (l : List X) (hx : x ∉ l) (A : Finset X) :
    pathFlow l x A = 0 := by
  induction l with
  | nil => simp
  | cons y l ih =>
      simp only [List.mem_cons, not_or] at hx
      simp [pathFlow_cons, unitEdge, hx.1, ih hx.2]

lemma pathFlow_eq_zero_or_one (l : List X) (hl : l.Nodup) (x : X) (A : Finset X) :
    pathFlow l x A = 0 ∨ pathFlow l x A = 1 := by
  induction l with
  | nil => simp
  | cons y l ih =>
      obtain ⟨hyn, hln⟩ := List.nodup_cons.mp hl
      by_cases hxy : x = y
      · subst x
        rw [pathFlow_cons, pathFlow_zero_of_not_mem l hyn]
        unfold unitEdge
        split_ifs <;> simp
      · simpa [pathFlow_cons, unitEdge, hxy] using ih hln

lemma pathFlow_head (y : X) (l : List X) (hyn : y ∉ l) :
    pathFlow (y :: l) y (y :: l).toFinset = 1 := by
  simp [pathFlow_cons, unitEdge, pathFlow_zero_of_not_mem l hyn]

lemma pathFlow_nonzero_mem (l : List X) (hp : pathFlow l x A ≠ 0) : x ∈ A := by
  induction l with
  | nil => simp at hp
  | cons y l ih =>
      by_cases hu : unitEdge y (y :: l).toFinset x A = 0
      · rw [pathFlow_cons, hu, zero_add] at hp
        exact ih hp
      · have heq : x = y ∧ A = (y :: l).toFinset := by simpa [unitEdge] using hu
        rcases heq with ⟨rfl, rfl⟩
        simp

/-- Divergence of the unit path of a duplicate-free list. -/
lemma pathFlow_divergence (l : List X) (hl : l.Nodup) (A : Finset X) :
    outflow (pathFlow l) A - inflow (pathFlow l) A =
      (if A = l.toFinset then 1 else 0) - (if A = ∅ then 1 else 0) := by
  induction l with
  | nil => simp only [outflow, inflow, pathFlow, Finset.sum_const_zero, List.toFinset_nil]; split_ifs <;> simp_all
  | cons y l ih =>
      have hyn : y ∉ l := (List.nodup_cons.mp hl).1
      have hln : l.Nodup := (List.nodup_cons.mp hl).2
      have hy : y ∈ (y :: l).toFinset := by simp
      have herase : (y :: l).toFinset.erase y = l.toFinset := by simp [hyn]
      change outflow (fun x B => unitEdge y (y :: l).toFinset x B + pathFlow l x B) A -
        inflow (fun x B => unitEdge y (y :: l).toFinset x B + pathFlow l x B) A = _
      rw [outflow_add, inflow_add, outflow_unitEdge hy, inflow_unitEdge hy, herase]
      have hi := ih hln
      linarith

lemma pathFlow_source (l : List X) (hl : l.Nodup) (hfull : l.toFinset = Finset.univ)
    [Nonempty X] : outflow (pathFlow l) Finset.univ = 1 := by
  have h := pathFlow_divergence l hl Finset.univ
  have hn : (Finset.univ : Finset X) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simpa [inflow, hfull, hn] using h

lemma pathFlow_conserve (l : List X) (hl : l.Nodup) (hfull : l.toFinset = Finset.univ)
    (A : Finset X) (hA : A.Nonempty) (hU : A ≠ Finset.univ) :
    outflow (pathFlow l) A = inflow (pathFlow l) A := by
  have h := pathFlow_divergence l hl A
  have hz : outflow (pathFlow l) A - inflow (pathFlow l) A = 0 := by
    simpa [hfull, hU, hA.ne_empty] using h
  exact sub_eq_zero.mp hz

end Falmagne
