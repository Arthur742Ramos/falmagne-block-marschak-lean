module

public import EconomicsNextProof.Path

@[expose] public section

namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}

lemma flow_outflow_nonneg (h : IsFlow q m) (A : Finset X) : 0 ≤ outflow q A := by
  exact Finset.sum_nonneg fun x hx => h.nonneg x A hx

lemma flow_edge_le_outflow (h : IsFlow q m) (hx : x ∈ A) : q x A ≤ outflow q A := by
  exact Finset.single_le_sum (fun y hy => h.nonneg y A hy) hx

lemma flow_inflow_nonneg (h : IsFlow q m) (A : Finset X) : 0 ≤ inflow q A := by
  apply Finset.sum_nonneg
  intro y hy
  exact h.nonneg y (insert y A) (Finset.mem_insert_self _ _)

lemma flow_zero_of_source_zero (h : IsFlow q 0) : ∀ A x, x ∈ A → q x A = 0 := by
  intro A
  induction hn : (Finset.univ \ A).card using Nat.strong_induction_on generalizing A with
  | h n ih =>
      intro x hx
      by_cases hU : A = Finset.univ
      · subst A
        have he := flow_edge_le_outflow h hx
        have hz := h.source
        have hnn := h.nonneg x Finset.univ hx
        linarith
      · have hA : A.Nonempty := ⟨x, hx⟩
        have hi : inflow q A = 0 := by
          unfold inflow
          apply Finset.sum_eq_zero
          intro y hy
          have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
          have hlt : (Finset.univ \ insert y A).card < n := by
            rw [← hn]
            apply Finset.card_lt_card
            constructor
            · intro z hz
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
                not_or] at hz ⊢
              exact hz.2
            · intro heq
              have hymem : y ∈ Finset.univ \ A := by simp [hyA]
              have := heq hymem
              simp at this
          exact ih _ hlt (insert y A) rfl y (Finset.mem_insert_self _ _)
        have hout : outflow q A = 0 := (h.conserve A hA hU).trans hi
        have he := flow_edge_le_outflow h hx
        have hnn := h.nonneg x A hx
        linarith

/-- A positive outgoing flow extends to a positive complete elimination path. -/
lemma exists_positive_path (h : IsFlow q m) (A : Finset X) (hpos : 0 < outflow q A) :
    ∃ l : List X, l.Nodup ∧ l.toFinset = A ∧
      ∀ x B, pathFlow l x B ≠ 0 → 0 < q x B := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
      obtain ⟨y, hy, hqy⟩ := (Finset.sum_pos_iff_of_nonneg (fun x hx => h.nonneg x A hx)).mp hpos
      by_cases he : A.erase y = ∅
      · have hsing : ({y} : Finset X) = A := by
          have hAi : insert y (A.erase y) = A := Finset.insert_erase hy
          simpa [he] using hAi
        refine ⟨[y], by simp, by simpa using hsing, ?_⟩
        intro x B hp
        simp [pathFlow, unitEdge] at hp
        obtain ⟨hxy, hB⟩ := hp
        rw [hxy, hB, hsing]
        exact hqy
      · have hAe : (A.erase y).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
        have hnotU : A.erase y ≠ Finset.univ := by
          intro heq
          have : y ∈ A.erase y := by rw [heq]; exact Finset.mem_univ y
          simp at this
        have hqin : q y A ≤ inflow q (A.erase y) := by
          have hymem : y ∈ Finset.univ \ A.erase y := by simp
          have hh := Finset.single_le_sum
            (fun z (hz : z ∈ Finset.univ \ A.erase y) =>
              h.nonneg z (insert z (A.erase y)) (Finset.mem_insert_self _ _)) hymem
          simpa [inflow, Finset.insert_erase hy] using hh
        have htailpos : 0 < outflow q (A.erase y) := by
          rw [h.conserve _ hAe hnotU]
          linarith
        obtain ⟨l, hln, hlA, hlpos⟩ :=
          ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem hy) (A.erase y) htailpos rfl
        have hyn : y ∉ l := by
          have : y ∉ l.toFinset := by rw [hlA]; simp
          simpa using this
        refine ⟨y :: l, List.nodup_cons.mpr ⟨hyn, hln⟩, ?_, ?_⟩
        · simp [hlA, Finset.insert_erase hy]
        · intro x B hp
          by_cases hu : unitEdge y (y :: l).toFinset x B = 0
          · apply hlpos x B
            rw [pathFlow_cons, hu, zero_add] at hp
            exact hp
          · have heq : x = y ∧ B = (y :: l).toFinset := by
              simpa [unitEdge] using hu
            obtain ⟨rfl, rfl⟩ := heq
            simpa [hlA, Finset.insert_erase hy] using hqy

noncomputable def edgeSupport (q : X → Finset X → ℝ) : Finset (X × Finset X) :=
  Finset.univ.filter fun e => e.1 ∈ e.2 ∧ 0 < q e.1 e.2

@[simp] lemma mem_edgeSupport (q : X → Finset X → ℝ) (e : X × Finset X) :
    e ∈ edgeSupport q ↔ e.1 ∈ e.2 ∧ 0 < q e.1 e.2 := by
  simp [edgeSupport]

/-- Remove a positive complete unit path at its smallest edge weight. -/
lemma flow_subtract_path [Nonempty X] (h : IsFlow q m) (hm : 0 < m) :
    ∃ (l : List X) (δ : ℝ), l.Nodup ∧ l.toFinset = Finset.univ ∧ 0 < δ ∧
      IsFlow (fun x A => q x A - δ * pathFlow l x A) (m - δ) ∧
      (edgeSupport (fun x A => q x A - δ * pathFlow l x A)).card < (edgeSupport q).card := by
  classical
  obtain ⟨l, hln, hfull, hpos⟩ := exists_positive_path h Finset.univ (by rw [h.source]; exact hm)
  let E : Finset (X × Finset X) := Finset.univ.filter fun e => pathFlow l e.1 e.2 ≠ 0
  have hEmem : ∀ e, e ∈ E ↔ pathFlow l e.1 e.2 ≠ 0 := by intro e; simp [E]
  have hEn : E.Nonempty := by
    cases l with
    | nil =>
        have hu : (Finset.univ : Finset X) = ∅ := hfull.symm
        exact (Finset.univ_nonempty.ne_empty hu).elim
    | cons y l =>
        refine ⟨(y, (y :: l).toFinset), ?_⟩
        rw [hEmem]
        rw [pathFlow_head y l (List.nodup_cons.mp hln).1]
        norm_num
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image E (fun e => q e.1 e.2) hEn
  let δ := q e.1 e.2
  have hδ : 0 < δ := hpos e.1 e.2 ((hEmem e).mp he)
  have hpe : pathFlow l e.1 e.2 = 1 :=
    (pathFlow_eq_zero_or_one l hln e.1 e.2).resolve_left ((hEmem e).mp he)
  have hnn : ∀ x A, x ∈ A → 0 ≤ q x A - δ * pathFlow l x A := by
    intro x A hx
    rcases pathFlow_eq_zero_or_one l hln x A with hp | hp
    · simpa [hp] using h.nonneg x A hx
    · have hE : (x, A) ∈ E := (hEmem _).mpr (by rw [hp]; norm_num)
      have hle := hmin (x, A) hE
      simpa [hp, δ] using sub_nonneg.mpr hle
  have hr : IsFlow (fun x A => q x A - δ * pathFlow l x A) (m - δ) := by
    refine ⟨hnn, ?_, ?_⟩
    · rw [outflow_sub, outflow_mul, h.source, pathFlow_source l hln hfull, mul_one]
    · intro A hA hU
      rw [outflow_sub, inflow_sub, outflow_mul, inflow_mul, h.conserve A hA hU,
        pathFlow_conserve l hln hfull A hA hU]
  refine ⟨l, δ, hln, hfull, hδ, hr, ?_⟩
  apply Finset.card_lt_card
  have hsub : edgeSupport (fun x A => q x A - δ * pathFlow l x A) ⊆ edgeSupport q := by
    intro z hz
    obtain ⟨hzm, hzpos⟩ := (mem_edgeSupport _ z).mp hz
    apply (mem_edgeSupport _ z).mpr
    refine ⟨hzm, ?_⟩
    have hpnn := pathFlow_nonneg l z.1 z.2
    have hδnn : 0 ≤ δ := le_of_lt hδ
    nlinarith
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have heqmem : e ∈ edgeSupport q := (mem_edgeSupport _ e).mpr
    ⟨pathFlow_nonzero_mem l ((hEmem e).mp he), hδ⟩
  rw [← heq] at heqmem
  have hfalse := ((mem_edgeSupport _ e).mp heqmem).2
  simp [δ, hpe] at hfalse

/-- Every nonnegative Boolean-lattice flow is a finite mixture of complete ranking paths.

This is proved by strong induction on the number of positive edges. Each step
subtracts the minimum edge weight of a positive complete path, annihilating
at least one edge. No flow decomposition theorem is assumed.
-/
theorem flow_decomposition [Nonempty X] (h : IsFlow q m) :
    ∃ μ : List X →₀ ℝ,
      (∀ l, 0 ≤ μ l) ∧
      (∀ l ∈ μ.support, l.Nodup ∧ l.toFinset = Finset.univ) ∧
      μ.sum (fun _ w => w) = m ∧
      (∀ x A, x ∈ A → μ.sum (fun l w => w * pathFlow l x A) = q x A) := by
  classical
  induction hn : (edgeSupport q).card using Nat.strong_induction_on generalizing q m with
  | h n ih =>
      by_cases hm0 : m = 0
      · subst m
        refine ⟨0, by simp, ?_, by simp, ?_⟩
        · intro l hl
          simp at hl
        · intro x A hx
          simpa using (flow_zero_of_source_zero h A x hx).symm
      · have hmnn : 0 ≤ m := by rw [← h.source]; exact flow_outflow_nonneg h _
        have hm : 0 < m := lt_of_le_of_ne hmnn (Ne.symm hm0)
        obtain ⟨l, δ, hln, hfull, hδ, hr, hlt⟩ := flow_subtract_path h hm
        obtain ⟨μ, hμnn, hμvalid, hμmass, hμedge⟩ :=
          ih _ (by simpa [hn] using hlt) hr rfl
        refine ⟨μ + Finsupp.single l δ, ?_, ?_, ?_, ?_⟩
        · intro k
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          split_ifs <;> linarith [hμnn k]
        · intro k hk
          have hku := Finsupp.support_add hk
          rcases Finset.mem_union.mp hku with hkm | hkl
          · exact hμvalid k hkm
          · have hkl' := (Finsupp.mem_support_single k l δ).mp hkl
            rw [hkl'.1]
            exact ⟨hln, hfull⟩
        · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl, hμmass]
          ring
        · intro x A hx
          rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
            Finsupp.sum_single_index (zero_mul _), hμedge x A hx]
          ring

end Falmagne
