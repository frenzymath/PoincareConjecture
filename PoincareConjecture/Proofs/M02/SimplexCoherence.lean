import PoincareConjecture.Proofs.M02.SimplexFaceHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

set_option autoImplicit false

universe w

open Set Topology CategoryTheory
open scoped unitInterval Simplicial

namespace PoincareConjecture.Proofs.M02

theorem stdSimplex_face_map_apply (n : ℕ) (i : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) (j : Fin (n + 1)) :
    stdSimplex.map i.succAbove z (i.succAbove j) = z j := by
  classical
  change FunOnFinite.linearMap ℝ ℝ i.succAbove z (i.succAbove j) = z j
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    exact (hkj (Fin.succAbove_right_injective (Finset.mem_filter.mp hk).2)).elim
  · intro hj
    exact (hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)).elim

theorem stdSimplex_face_map_injective (n : ℕ) (i : Fin (n + 2)) :
    Function.Injective (stdSimplex.map (S := ℝ) i.succAbove) := by
  intro z w heq
  apply stdSimplex.ext
  funext j
  have h := congrArg (fun y : stdSimplex ℝ (Fin (n + 2)) => y (i.succAbove j)) heq
  simpa only [stdSimplex_face_map_apply] using h

theorem stdSimplex_face_map_comp (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map i.succAbove (stdSimplex.map j.succAbove z) =
      stdSimplex.map (i.succAbove j).succAbove (stdSimplex.map (j.predAbove i).succAbove z) := by
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  apply congrArg (fun a : Fin (n + 1) → Fin (n + 3) => stdSimplex.map a z)
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm

theorem exists_stdSimplex_face_intersection (n : ℕ) (i : Fin (n + 3)) (j : Fin (n + 2))
    (z w : stdSimplex ℝ (Fin (n + 2)))
    (heq : stdSimplex.map i.succAbove z = stdSimplex.map (i.succAbove j).succAbove w) :
    ∃ u : stdSimplex ℝ (Fin (n + 1)),
      z = stdSimplex.map j.succAbove u ∧ w = stdSimplex.map (j.predAbove i).succAbove u := by
  classical
  have hzj : z j = 0 := by
    rw [← stdSimplex_face_map_apply (n + 1) i z j]
    rw [heq]
    change FunOnFinite.linearMap ℝ ℝ (i.succAbove j).succAbove w (i.succAbove j) = 0
    rw [FunOnFinite.linearMap_apply_apply]
    simp [Fin.succAbove_ne]
  have hsum : ∑ k : Fin (n + 1), z (j.succAbove k) = 1 := by
    have hs := Fin.sum_univ_succAbove (fun k => z k) j
    simpa only [stdSimplex.sum_eq_one, hzj, zero_add] using hs.symm
  let u : stdSimplex ℝ (Fin (n + 1)) :=
    ⟨fun k => z (j.succAbove k), fun k => z.property.1 _, hsum⟩
  have hu : stdSimplex.map j.succAbove u = z := by
    apply stdSimplex.ext
    funext k
    rcases Fin.eq_self_or_eq_succAbove j k with hk | ⟨l, hk⟩
    · rw [hk]
      change FunOnFinite.linearMap ℝ ℝ j.succAbove u j = z j
      rw [hzj, FunOnFinite.linearMap_apply_apply]
      simp [Fin.succAbove_ne]
    · rw [hk]
      exact stdSimplex_face_map_apply n j u l
  have hw : stdSimplex.map (i.succAbove j).succAbove
      (stdSimplex.map (j.predAbove i).succAbove u) =
        stdSimplex.map (i.succAbove j).succAbove w :=
    (stdSimplex_face_map_comp n i j u).symm.trans
      ((congrArg (stdSimplex.map i.succAbove) hu).trans heq)
  exact ⟨u, hu.symm, ((stdSimplex_face_map_injective (n + 1) (i.succAbove j)) hw).symm⟩

theorem stdSimplex_face_homotopies_agree_of_double_faces
    (n : ℕ) {X : Type*} [TopologicalSpace X]
    (h : Fin (n + 3) → C(unitInterval × stdSimplex ℝ (Fin (n + 2)), X))
    (hdouble : ∀ (i : Fin (n + 3)) (j : Fin (n + 2)) (t : unitInterval)
      (u : stdSimplex ℝ (Fin (n + 1))),
      h i (t, stdSimplex.map j.succAbove u) =
        h (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove u)) :
    ∀ (i k : Fin (n + 3)) (z w : stdSimplex ℝ (Fin (n + 2))) (t : unitInterval),
      stdSimplex.map i.succAbove z = stdSimplex.map k.succAbove w → h i (t, z) = h k (t, w) := by
  intro i k z w t heq
  by_cases hik : i = k
  · subst k
    have hzw := stdSimplex_face_map_injective (n + 1) i heq
    cases hzw
    rfl
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hik)
    obtain ⟨u, rfl, rfl⟩ := exists_stdSimplex_face_intersection n i j z w heq
    exact hdouble i j t u

theorem stdSimplex_interval_face_homotopies_agree
    {X : Type*} [TopologicalSpace X]
    (h : Fin 2 → C(unitInterval × stdSimplex ℝ (Fin 1), X)) :
    ∀ (i j : Fin 2) (z w : stdSimplex ℝ (Fin 1)) (t : unitInterval),
      stdSimplex.map i.succAbove z = stdSimplex.map j.succAbove w → h i (t, z) = h j (t, w) := by
  intro i j z w t heq
  by_cases hij : i = j
  · subst j
    have hzw := stdSimplex_face_map_injective 0 i heq
    cases hzw
    rfl
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
    have hleft : stdSimplex.map i.succAbove z i = 0 := by
      change FunOnFinite.linearMap ℝ ℝ i.succAbove z i = 0
      rw [FunOnFinite.linearMap_apply_apply]
      simp [Fin.succAbove_ne]
    have hright : stdSimplex.map j.succAbove w i = 1 := by
      rw [← hk, stdSimplex_face_map_apply]
      exact stdSimplex.eq_one_of_unique w k
    exact (zero_ne_one (hleft.symm.trans
      ((congrArg (fun y : stdSimplex ℝ (Fin 2) => y i) heq).trans hright))).elim

theorem singularSimplex_double_face (X : TopCat.{w}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n + 2⦌) (i : Fin (n + 3)) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ j ((TopCat.toSSet.obj X).δ i s) =
      (TopCat.toSSet.obj X).δ (j.predAbove i) ((TopCat.toSSet.obj X).δ (i.succAbove j) s) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [TopCat.toSSetObjEquiv_δ_apply]
  exact congrArg (X.toSSetObjEquiv _ s) (stdSimplex_face_map_comp n i j z)

theorem exists_stdSimplex_homotopy_extension (n : ℕ) {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin (n + 1)), X))
    (h : C(unitInterval × {y : stdSimplex ℝ (Fin (n + 1)) // ∃ i, y i = 0}, X))
    (h0 : ∀ z : {y : stdSimplex ℝ (Fin (n + 1)) // ∃ i, y i = 0}, h (0, z) = f z) :
    ∃ F : C(unitInterval × stdSimplex ℝ (Fin (n + 1)), X),
      (∀ z, F (0, z) = f z) ∧
        ∀ (t : unitInterval) (z : {y : stdSimplex ℝ (Fin (n + 1)) // ∃ i, y i = 0}),
          F (t, z) = h (t, z) := by
  obtain ⟨e, he⟩ := exists_stdSimplex_cube_pair_homeomorph n
  let b : C(Cube.boundary (Fin n),
      {y : stdSimplex ℝ (Fin (n + 1)) // ∃ i, y i = 0}) := {
    toFun := fun z => ⟨e.symm z, (he _).mpr (by simpa only [e.apply_symm_apply] using z.property)⟩
    continuous_toFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _
  }
  let f' : C(I^(Fin n), X) := f.comp ⟨e.symm, e.symm.continuous⟩
  let h' : C(unitInterval × Cube.boundary (Fin n), X) :=
    h.comp ⟨fun z => (z.1, b z.2), continuous_fst.prodMk (b.continuous.comp continuous_snd)⟩
  obtain ⟨G, hG0, hGB⟩ := exists_cube_homotopy_extension f' h' (fun z => h0 (b z))
  let F : C(unitInterval × stdSimplex ℝ (Fin (n + 1)), X) :=
    G.comp ⟨fun z => (z.1, e z.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  refine ⟨F, fun z => (hG0 (e z)).trans (congrArg f (e.symm_apply_apply z)), fun t z => ?_⟩
  have hz : e z.val ∈ Cube.boundary (Fin n) := (he _).mp z.property
  have hb : b ⟨e z.val, hz⟩ = z := Subtype.ext (e.symm_apply_apply z.val)
  exact (hGB t ⟨e z.val, hz⟩).trans (congrArg (fun w => h (t, w)) hb)

end PoincareConjecture.Proofs.M02
