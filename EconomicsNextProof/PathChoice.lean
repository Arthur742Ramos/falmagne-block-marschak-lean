module

public import EconomicsNextProof.Path
public import EconomicsNextProof.Representation

@[expose] public section

namespace Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {x y : X} {A : Finset X}

lemma lowerContour_cons_self (h : x ∉ l) :
    lowerContour (x :: l) x = (x :: l).toFinset := by
  ext y
  simp [lowerContour]

lemma lowerContour_cons_of_ne (hxy : x ≠ y) (hyn : y ∉ l) :
    lowerContour (y :: l) x = lowerContour l x := by
  ext z
  by_cases hz : z = y
  · subst z
    simp [lowerContour, hyn, List.idxOf_cons_ne l hxy.symm]
  · simp [lowerContour, hz, List.idxOf_cons_ne l hxy.symm, List.idxOf_cons_ne l (Ne.symm hz)]

lemma pathFlow_eq_lowerContour (hl : l.Nodup) (hx : x ∈ l) :
    pathFlow l x A = if A = lowerContour l x then 1 else 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
      obtain ⟨hyn, hln⟩ := List.nodup_cons.mp hl
      by_cases hxy : x = y
      · subst x
        rw [pathFlow_cons, pathFlow_zero_of_not_mem l hyn, add_zero,
          lowerContour_cons_self hyn]
        simp [unitEdge]
      · have hx' : x ∈ l := (List.mem_cons.mp hx).resolve_left hxy
        rw [pathFlow_cons, lowerContour_cons_of_ne hxy hyn, ih hln hx']
        simp [unitEdge, hxy]

lemma pathFlow_eq_rankingEdge (hl : IsRanking l) :
    pathFlow l x A = rankingEdge l x A := by
  rw [pathFlow_eq_lowerContour hl.1 (ranking_mem hl x)]
  unfold rankingEdge
  by_cases hA : A = lowerContour l x
  · subst A
    simp [self_mem_lowerContour hl x]
  · simp [hA]

end Falmagne
