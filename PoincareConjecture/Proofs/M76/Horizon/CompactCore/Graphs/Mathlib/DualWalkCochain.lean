import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualFaceGraph










set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

open Classical

variable {V : Type*} [Fintype V] (A : PreAbstractSimplicialComplex V)
  (P : SimpleGraph V)
  (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)


noncomputable def dualWalkCochain {u v : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u v) : Edge A → ZMod 2 :=
  match w with
  | .nil => 0
  | .cons h p =>
    Pi.single (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(_, _), h⟩).val 1 +
      dualWalkCochain p


theorem edgeCoboundary_complementary_single {u v : Triangle A}
    (h : (complementaryTriangleGraph A P).Adj u v) :
    edgeCoboundary A
        (Pi.single (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(u, v), h⟩).val 1) =
      Pi.single u 1 + Pi.single v 1 := by
  classical
  ext t
  rw [edgeCoboundary_single]
  have hmem :
      (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(u, v), h⟩).val.val ⊆ t.val ↔
        t = u ∨ t = v := by
    have hc := complementaryTriangleEdgeEquiv_cofaces A P hcofaces ⟨s(u, v), h⟩
    have hm := congrArg (fun s : Finset (Triangle A) => t ∈ s) hc
    simpa only [triangleCofaces, Finset.mem_filter, Finset.mem_univ, true_and,
      Sym2.mem_toFinset, Sym2.mem_iff] using Iff.of_eq hm
  simp only [hmem]
  by_cases hu : t = u <;> by_cases hv : t = v
  · exact (h.ne (hu.symm.trans hv)).elim
  · simp [hu, h.ne]
  · simp [hv, h.ne.symm]
  · simp [hu, hv]


theorem edgeCoboundary_dualWalkCochain {u v : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u v) :
    edgeCoboundary A (dualWalkCochain A P hcofaces w) =
      Pi.single u 1 + Pi.single v 1 := by
  induction w with
  | nil => ext t; simp [dualWalkCochain, CharTwo.add_self_eq_zero]
  | @cons u v w h p ih =>
    rw [dualWalkCochain, map_add, edgeCoboundary_complementary_single, ih]
    ext t
    simp only [Pi.add_apply]
    calc
      _ = Pi.single u 1 t +
          ((Pi.single v 1 t + Pi.single v 1 t) + Pi.single w 1 t) := by abel_nf
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]


theorem dualWalkCochain_closed {u : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u u) :
    edgeCoboundary A (dualWalkCochain A P hcofaces w) = 0 := by
  rw [edgeCoboundary_dualWalkCochain]
  ext t
  exact CharTwo.add_self_eq_zero _


theorem dualWalkCochain_eq_zero_on_primal {u v : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u v) (e : Edge A)
    (he : edgeInGraph A P e) : dualWalkCochain A P hcofaces w e = 0 := by
  classical
  induction w with
  | nil => rfl
  | @cons u v w h p ih =>
    have hne : (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(u, v), h⟩).val ≠ e := by
      intro hEq
      exact (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(u, v), h⟩).property
        (hEq.symm ▸ he)
    simp [dualWalkCochain, Ne.symm hne, ih]


theorem dualWalkCochain_eq_count {u v : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u v)
    (s : (complementaryTriangleGraph A P).edgeSet) :
    dualWalkCochain A P hcofaces w
      (complementaryTriangleEdgeEquiv A P hcofaces s).val =
        (w.edges.count s.val : ZMod 2) := by
  classical
  induction w with
  | nil => simp [dualWalkCochain]
  | @cons u v w h p ih =>
    have heq :
        (complementaryTriangleEdgeEquiv A P hcofaces ⟨s(u, v), h⟩).val =
          (complementaryTriangleEdgeEquiv A P hcofaces s).val ↔ s(u, v) = s.val := by
      constructor
      · intro he
        exact congrArg Subtype.val
          ((complementaryTriangleEdgeEquiv A P hcofaces).injective (Subtype.ext he))
      · intro he
        exact congrArg (fun r => (complementaryTriangleEdgeEquiv A P hcofaces r).val)
          (Subtype.ext he)
    by_cases hs : s(u, v) = s.val
    · have hl := heq.mpr hs
      simp [dualWalkCochain, ih, SimpleGraph.Walk.edges_cons, hs, add_comm]
    · have hl := mt heq.mp hs
      simp [dualWalkCochain, Ne.symm hl, ih, SimpleGraph.Walk.edges_cons, hs]


theorem dualWalkCochain_eq_one_of_isTrail {u v : Triangle A}
    (w : (complementaryTriangleGraph A P).Walk u v) (hw : w.IsTrail)
    (s : (complementaryTriangleGraph A P).edgeSet) (hs : s.val ∈ w.edges) :
    dualWalkCochain A P hcofaces w
      (complementaryTriangleEdgeEquiv A P hcofaces s).val = 1 := by
  rw [dualWalkCochain_eq_count, hw.count_edges_eq_one hs]
  rfl

end PreAbstractSimplicialComplex.ModTwoCochains
