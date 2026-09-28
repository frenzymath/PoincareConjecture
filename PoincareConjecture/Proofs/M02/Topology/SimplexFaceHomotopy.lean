import PoincareConjecture.Proofs.M02.Topology.SingularKan
import Mathlib.Topology.Homotopy.Affine
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem stdSimplex_adjacent_faces_eq_of_zero (n : Nat) (i : Fin (n + 1))
    (z : stdSimplex Real (Fin (n + 1))) (hz : z i = 0) :
    stdSimplex.map i.castSucc.succAbove z = stdSimplex.map i.succ.succAbove z := by
  cases n with
  | zero =>
    have hs := z.property.2
    rw [Fin.sum_univ_one, ← Fin.eq_zero i] at hs
    exact False.elim (zero_ne_one (hz.symm.trans hs))
  | succ n =>
    obtain ⟨t, rfl⟩ := (stdSimplex_face_range_iff n i z).mpr hz
    have h := stdSimplex_two_face_comp n i.castSucc i.succ
      (Fin.castSucc_lt_succ_iff.mpr le_rfl) t
    rw [Fin.pred_succ, Fin.castPred_castSucc] at h
    exact h

theorem stdSimplex_adjacent_faces_homotopicRel
    {X : Type u} [TopologicalSpace X] (n : Nat) (i : Fin (n + 1))
    (F : C(stdSimplex Real (Fin (n + 2)), X)) (x : X)
    (hF : forall (j : Fin (n + 2)), Ne j i.castSucc -> Ne j i.succ ->
      forall z : stdSimplex Real (Fin (n + 1)), F (stdSimplex.map j.succAbove z) = x) :
    ContinuousMap.HomotopicRel
      (F.comp (ContinuousMap.mk (stdSimplex.map i.castSucc.succAbove)
        (stdSimplex.continuous_map _)))
      (F.comp (ContinuousMap.mk (stdSimplex.map i.succ.succAbove)
        (stdSimplex.continuous_map _)))
      (Set.ofPred (fun z : stdSimplex Real (Fin (n + 1)) =>
        Exists fun k : Fin (n + 1) => z k = 0)) := by
  let a : C(stdSimplex Real (Fin (n + 1)), stdSimplex Real (Fin (n + 2))) :=
    ⟨stdSimplex.map i.castSucc.succAbove, stdSimplex.continuous_map _⟩
  let b : C(stdSimplex Real (Fin (n + 1)), stdSimplex Real (Fin (n + 2))) :=
    ⟨stdSimplex.map i.succ.succAbove, stdSimplex.continuous_map _⟩
  let A : C(stdSimplex Real (Fin (n + 1)), Fin (n + 2) → Real) :=
    ⟨fun z => (a z).val, continuous_subtype_val.comp a.continuous⟩
  let B : C(stdSimplex Real (Fin (n + 1)), Fin (n + 2) → Real) :=
    ⟨fun z => (b z).val, continuous_subtype_val.comp b.continuous⟩
  let H := ContinuousMap.Homotopy.affine A B
  have hm (p : unitInterval × stdSimplex Real (Fin (n + 1))) :
      H p ∈ stdSimplex Real (Fin (n + 2)) :=
    (convex_stdSimplex Real _).lineMap_mem (a p.2).property (b p.2).property p.1.property
  have hzero (j : Fin (n + 2)) (hj0 : j ≠ i.castSucc) (hj1 : j ≠ i.succ)
      (q : stdSimplex Real (Fin (n + 2))) (hq : q j = 0) : F q = x := by
    obtain ⟨z, rfl⟩ := (stdSimplex_face_range_iff n j q).mpr hq
    exact hF j hj0 hj1 z
  refine ⟨{ toFun := fun p => F ⟨H p, hm p⟩
            continuous_toFun := F.continuous.comp (H.continuous.subtype_mk hm)
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro z
    apply congrArg F
    exact Subtype.ext (H.apply_zero z)
  · intro z
    apply congrArg F
    exact Subtype.ext (H.apply_one z)
  · intro t z hz
    obtain ⟨k, hk⟩ := hz
    change F ⟨H (t, z), hm (t, z)⟩ = F (a z)
    by_cases hki : k = i
    · subst k
      have hab : a z = b z := stdSimplex_adjacent_faces_eq_of_zero n i z hk
      apply congrArg F
      apply Subtype.ext
      change AffineMap.lineMap (a z).val (b z).val (t : Real) = (a z).val
      rw [← hab, AffineMap.lineMap_same_apply]
    · have hj : i.castSucc.succAbove k = i.succ.succAbove k := by
        rcases lt_or_gt_of_ne hki with hki | hik
        · rw [Fin.succAbove_castSucc_of_lt _ _ hki,
            Fin.succAbove_succ_of_le _ _ hki.le]
        · rw [Fin.succAbove_castSucc_of_le _ _ hik.le,
            Fin.succAbove_succ_of_lt _ _ hik]
      have hj0 : i.castSucc.succAbove k ≠ i.castSucc := Fin.succAbove_ne _ _
      have hj1 : i.castSucc.succAbove k ≠ i.succ := by
        rw [hj]
        exact Fin.succAbove_ne _ _
      have ha : a z (i.castSucc.succAbove k) = 0 :=
        (stdSimplex_face_succAbove n i.castSucc z k).trans hk
      have hb : b z (i.castSucc.succAbove k) = 0 := by
        rw [hj]
        exact (stdSimplex_face_succAbove n i.succ z k).trans hk
      have ht : H (t, z) (i.castSucc.succAbove k) = 0 := by
        change AffineMap.lineMap (a z).val (b z).val (t : Real) _ = 0
        rw [AffineMap.lineMap_apply_module]
        change (1 - (t : Real)) * a z _ + (t : Real) * b z _ = 0
        rw [ha, hb, mul_zero, mul_zero, add_zero]
      exact (hzero _ hj0 hj1 ⟨H (t, z), hm (t, z)⟩ ht).trans
        (hzero _ hj0 hj1 (a z) ha).symm

theorem singular_const_apply (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (z : stdSimplex Real (Fin (n + 1))) :
    X.toSSetObjEquiv _ (SSet.yonedaEquiv
      (SSet.const (X := SSet.stdSimplex.{u}.obj (SimplexCategory.mk n)) x)) z =
      TopCat.toSSetObj₀Equiv x := by
  change X.toSSetObjEquiv _
    ((TopCat.toSSet.obj X).map ((SimplexCategory.mk n).const _ 0).op x) z = _
  rw [TopCat.toSSetObjEquiv_naturality_apply]
  change X.toSSetObjEquiv _ x _ = X.toSSetObjEquiv _ x default
  exact congrArg (X.toSSetObjEquiv _ x) (Subsingleton.elim _ _)

theorem singular_relStruct_homotopicRel (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (f g : (TopCat.toSSet.obj X).PtSimplex n x) (i : Fin (n + 1))
    (r : SSet.PtSimplex.RelStruct f g i) :
    ContinuousMap.HomotopicRel
      (X.toSSetObjEquiv _ (SSet.yonedaEquiv f.map))
      (X.toSSetObjEquiv _ (SSet.yonedaEquiv g.map))
      (Set.ofPred (fun z : stdSimplex Real (Fin (n + 1)) =>
        Exists fun k : Fin (n + 1) => z k = 0)) := by
  let F := X.toSSetObjEquiv _ (SSet.yonedaEquiv r.map)
  have hF (j : Fin (n + 2)) (hj0 : j ≠ i.castSucc) (hj1 : j ≠ i.succ)
      (z : stdSimplex Real (Fin (n + 1))) :
      F (stdSimplex.map j.succAbove z) = TopCat.toSSetObj₀Equiv x := by
    have hr : SSet.stdSimplex.δ j ≫ r.map = SSet.const x := by
      by_cases hj : j < i.castSucc
      · exact r.δ_map_of_lt j hj
      · have hij : i.castSucc < j := lt_of_le_of_ne (le_of_not_gt hj) hj0.symm
        have hsj : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hij
        exact r.δ_map_of_gt j (lt_of_le_of_ne hsj hj1.symm)
    have h := congrArg (fun q : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
      X.toSSetObjEquiv _ (SSet.yonedaEquiv q) z) hr
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply,
      singular_const_apply] at h
    exact h
  obtain ⟨H⟩ := stdSimplex_adjacent_faces_homotopicRel n i F
    (TopCat.toSSetObj₀Equiv x) hF
  refine ⟨H.cast ?_ ?_⟩
  · ext z
    have h := congrArg (fun q : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
      X.toSSetObjEquiv _ (SSet.yonedaEquiv q) z) r.δ_castSucc_map
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply] at h
    exact h
  · ext z
    have h := congrArg (fun q : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
      X.toSSetObjEquiv _ (SSet.yonedaEquiv q) z) r.δ_succ_map
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, TopCat.toSSetObjEquiv_δ_apply] at h
    exact h

end PoincareConjecture.Proofs.M02.Topology
