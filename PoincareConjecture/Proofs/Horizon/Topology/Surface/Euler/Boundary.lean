


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence







set_option autoImplicit false

namespace PoincareConjecture.Topology.Surface.Euler

open PoincareConjecture.Surface.Combinatorial.Incidence


theorem incidenceMatrix_eq_of_pair_eq {V E : Type*} [DecidableEq V] (ends : E → V × V)
    (e : E) (a b : V) (h : ({(ends e).1, (ends e).2} : Set V) = {a, b})
    (v : V) : incidenceMatrix ends e v =
      (if a = v then 1 else 0) + (if b = v then 1 else 0) := by
  classical
  rcases Set.pair_eq_pair_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp only [incidenceMatrix, h₁, h₂]
  · simp only [incidenceMatrix, h₁, h₂, add_comm]


theorem incidenceMatrix_eq_sum_faceEdge {E F : Type*} [DecidableEq E]
    (faceEdge : F → Fin 3 → E) (adjacent : E → F × F)
    (hinj : ∀ f, Function.Injective (faceEdge f))
    (hdist : ∀ e, (adjacent e).1 ≠ (adjacent e).2)
    (hmem : ∀ e f, (∃ k, faceEdge f k = e) ↔
      f = (adjacent e).1 ∨ f = (adjacent e).2) (e : E) (f : F) :
    incidenceMatrix adjacent e f =
      ∑ k : Fin 3, (if faceEdge f k = e then (1 : ZMod 2) else 0) := by
  classical
  by_cases he : ∃ k, faceEdge f k = e
  · obtain ⟨k, rfl⟩ := he
    have hs : (∑ j : Fin 3,
        if faceEdge f j = faceEdge f k then (1 : ZMod 2) else 0) = 1 := by
      simp only [(hinj f).eq_iff]
      simp
    rw [hs]
    rcases (hmem (faceEdge f k) f).mp ⟨k, rfl⟩ with h | h
    · have hne : (adjacent (faceEdge f k)).2 ≠ f := by
        intro hh
        exact hdist (faceEdge f k) (h.symm.trans hh.symm)
      simp only [incidenceMatrix, if_pos h.symm, if_neg hne, add_zero]
    · have hne : (adjacent (faceEdge f k)).1 ≠ f := by
        intro hh
        exact hdist (faceEdge f k) (hh.trans h)
      simp only [incidenceMatrix, if_pos h.symm, if_neg hne, zero_add]
  · have hf := not_or.mp (mt (hmem e f).mpr he)
    simp only [incidenceMatrix, if_neg (Ne.symm hf.1), if_neg (Ne.symm hf.2),
      zero_add]
    symm
    apply Finset.sum_eq_zero
    intro k _
    exact if_neg (fun hk => he ⟨k, hk⟩)


theorem boundary_comp_eq_zero {V E F : Type*} [Fintype E]
    (faceEdge : F → Fin 3 → E) (corner : F → Fin 3 → V)
    (ends : E → V × V) (adjacent : E → F × F)
    (hinj : ∀ f, Function.Injective (faceEdge f))
    (hdist : ∀ e, (adjacent e).1 ≠ (adjacent e).2)
    (hmem : ∀ e f, (∃ k, faceEdge f k = e) ↔
      f = (adjacent e).1 ∨ f = (adjacent e).2)
    (hends : ∀ f k,
      ({(ends (faceEdge f k)).1, (ends (faceEdge f k)).2} : Set V) =
        {corner f (k.succAbove 0), corner f (k.succAbove 1)}) :
    (incidenceMatrix ends).transpose * incidenceMatrix adjacent = 0 := by
  classical
  ext v f
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  simp_rw [incidenceMatrix_eq_sum_faceEdge faceEdge adjacent hinj hdist hmem,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp_rw [incidenceMatrix_eq_of_pair_eq ends _ _ _ (hends f _)]
  simp only [Fin.sum_univ_succ, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  change ((if corner f 1 = v then 1 else 0) + (if corner f 2 = v then 1 else 0)) +
    (((if corner f 0 = v then 1 else 0) + (if corner f 2 = v then 1 else 0)) +
    ((if corner f 0 = v then 1 else 0) + (if corner f 1 = v then 1 else 0))) = 0
  let a : ZMod 2 := if corner f 0 = v then 1 else 0
  let b : ZMod 2 := if corner f 1 = v then 1 else 0
  let c : ZMod 2 := if corner f 2 = v then 1 else 0
  change (b + c) + ((a + c) + (a + b)) = 0
  calc
    _ = (a + a) + (b + b) + (c + c) := by ring
    _ = 0 := by simp only [CharTwo.add_self_eq_zero]


theorem eqvGen_endpoints_of_pair_eq {V E : Type*} (ends : E → V × V)
    (e : E) (a b : V) (h : ({(ends e).1, (ends e).2} : Set V) = {a, b}) :
    Relation.EqvGen (fun x y => ∃ e, ends e = (x, y)) a b := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .rel _ _ ⟨e, Prod.ext h₁ h₂⟩
  · exact .symm _ _ (.rel _ _ ⟨e, Prod.ext h₁ h₂⟩)


theorem eqvGen_triangle_corners {V E F : Type*}
    (faceEdge : F → Fin 3 → E) (corner : F → Fin 3 → V) (ends : E → V × V)
    (hends : ∀ f k,
      ({(ends (faceEdge f k)).1, (ends (faceEdge f k)).2} : Set V) =
        {corner f (k.succAbove 0), corner f (k.succAbove 1)})
    (f : F) (i j : Fin 3) :
    Relation.EqvGen (fun x y => ∃ e, ends e = (x, y)) (corner f i) (corner f j) := by
  have h₁ := eqvGen_endpoints_of_pair_eq ends (faceEdge f 2) _ _ (hends f 2)
  have h₂ := eqvGen_endpoints_of_pair_eq ends (faceEdge f 1) _ _ (hends f 1)
  change Relation.EqvGen _ (corner f 0) (corner f 1) at h₁
  change Relation.EqvGen _ (corner f 0) (corner f 2) at h₂
  have hbase : ∀ k, Relation.EqvGen (fun x y => ∃ e, ends e = (x, y))
      (corner f 0) (corner f k) := by
    intro k
    fin_cases k
    · exact .refl _
    · exact h₁
    · exact h₂
  exact .trans _ _ _ (.symm _ _ (hbase i)) (hbase j)


theorem endpointConnected_of_dual {V E F : Type*}
    (faceEdge : F → Fin 3 → E) (corner : F → Fin 3 → V)
    (ends : E → V × V) (adjacent : E → F × F)
    (hmem : ∀ e f, (∃ k, faceEdge f k = e) ↔
      f = (adjacent e).1 ∨ f = (adjacent e).2)
    (hends : ∀ f k,
      ({(ends (faceEdge f k)).1, (ends (faceEdge f k)).2} : Set V) =
        {corner f (k.succAbove 0), corner f (k.succAbove 1)})
    (hsurj : ∀ v, ∃ f k, corner f k = v)
    (hdual : EndpointConnected adjacent) : EndpointConnected ends := by
  have hcorner : ∀ e f, (f = (adjacent e).1 ∨ f = (adjacent e).2) →
      ∃ i, corner f i = (ends e).1 := by
    intro e f hf
    obtain ⟨k, hk⟩ := (hmem e f).mpr hf
    have hh : (ends e).1 ∈
        ({corner f (k.succAbove 0), corner f (k.succAbove 1)} : Set V) := by
      rw [← hends f k, hk]
      exact Set.mem_insert _ _
    rcases Set.mem_insert_iff.mp hh with h | h
    · exact ⟨_, h.symm⟩
    · exact ⟨_, (Set.mem_singleton_iff.mp h).symm⟩
  have hstep : ∀ f g, (∃ e, adjacent e = (f, g)) →
      Relation.EqvGen (fun x y => ∃ e, ends e = (x, y)) (corner f 0) (corner g 0) := by
    rintro f g ⟨e, he⟩
    obtain ⟨i, hi⟩ := hcorner e f (Or.inl (congrArg Prod.fst he).symm)
    obtain ⟨j, hj⟩ := hcorner e g (Or.inr (congrArg Prod.snd he).symm)
    have hf := eqvGen_triangle_corners faceEdge corner ends hends f 0 i
    have hg := eqvGen_triangle_corners faceEdge corner ends hends g j 0
    rw [hi] at hf
    rw [hj] at hg
    exact .trans _ _ _ hf hg
  have hfaces : ∀ f g,
      Relation.EqvGen (fun x y => ∃ e, ends e = (x, y)) (corner f 0) (corner g 0) := by
    intro f g
    induction hdual f g with
    | rel a b hab => exact hstep a b hab
    | refl a => exact .refl _
    | symm a b hab ih => exact .symm _ _ ih
    | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  intro v w
  obtain ⟨f, i, rfl⟩ := hsurj v
  obtain ⟨g, j, rfl⟩ := hsurj w
  exact .trans _ _ _ (eqvGen_triangle_corners faceEdge corner ends hends f i 0)
    (.trans _ _ _ (hfaces f g) (eqvGen_triangle_corners faceEdge corner ends hends g 0 j))

end PoincareConjecture.Topology.Surface.Euler
