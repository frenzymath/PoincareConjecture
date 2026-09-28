import PoincareConjecture.Proofs.M02.Topology.SimplexHornFilling
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

set_option autoImplicit false

open CategoryTheory Simplicial
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem stdSimplex_face_map_injective (n : Nat) (i : Fin (n + 2)) :
    Function.Injective (stdSimplex.map (S := Real) i.succAbove) := by
  intro z w h
  apply Subtype.ext
  funext l
  calc
    z l = stdSimplex.map i.succAbove z (i.succAbove l) :=
      (stdSimplex_face_succAbove n i z l).symm
    _ = stdSimplex.map i.succAbove w (i.succAbove l) :=
      DFunLike.congr_fun h (i.succAbove l)
    _ = w l := stdSimplex_face_succAbove n i w l

theorem stdSimplex_two_face_comp (n : Nat) (j k : Fin (n + 3)) (hjk : j < k)
    (t : stdSimplex Real (Fin (n + 1))) :
    stdSimplex.map j.succAbove
      (stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove t) =
    stdSimplex.map k.succAbove
      (stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove t) := by
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  apply congrArg (fun a : Fin (n + 1) → Fin (n + 3) => stdSimplex.map a t)
  funext l
  have h := Fin.succAbove_succAbove_succAbove_predAbove j
    (k.pred (Fin.ne_zero_of_lt hjk)) l
  rw [Fin.succAbove_pred_of_lt j k hjk, Fin.predAbove_pred_of_lt k j hjk] at h
  exact h.symm

theorem exists_stdSimplex_two_face_preimage (n : Nat) (j k : Fin (n + 3))
    (hjk : j < k) (z w : stdSimplex Real (Fin (n + 2)))
    (hzw : stdSimplex.map j.succAbove z = stdSimplex.map k.succAbove w) :
    ∃ t : stdSimplex Real (Fin (n + 1)),
      stdSimplex.map (k.pred (Fin.ne_zero_of_lt hjk)).succAbove t = z ∧
        stdSimplex.map (j.castPred (Fin.ne_last_of_lt hjk)).succAbove t = w := by
  have hzk : z (k.pred (Fin.ne_zero_of_lt hjk)) = 0 := by
    calc
      z (k.pred (Fin.ne_zero_of_lt hjk)) =
          stdSimplex.map j.succAbove z (j.succAbove (k.pred (Fin.ne_zero_of_lt hjk))) :=
        (stdSimplex_face_succAbove (n + 1) j z _).symm
      _ = stdSimplex.map j.succAbove z k := by rw [Fin.succAbove_pred_of_lt j k hjk]
      _ = stdSimplex.map k.succAbove w k := DFunLike.congr_fun hzw k
      _ = 0 := stdSimplex_face_zero (n + 1) k w
  obtain ⟨t, ht⟩ :=
    (stdSimplex_face_range_iff n (k.pred (Fin.ne_zero_of_lt hjk)) z).mpr hzk
  refine ⟨t, ht, stdSimplex_face_map_injective (n + 1) k ?_⟩
  rw [← stdSimplex_two_face_comp n j k hjk t, ht]
  exact hzw

theorem singular_horn_faces_agree (X : TopCat.{u}) (n : Nat) (i : Fin (n + 2))
    (f : ∀ j : Fin (n + 2), j ≠ i → ((Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X))
    (hf : SSet.horn.IsCompatible f)
    (j k : Fin (n + 2)) (hj : j ≠ i) (hk : k ≠ i)
    (z w : stdSimplex Real (Fin (n + 1)))
    (hzw : stdSimplex.map j.succAbove z = stdSimplex.map k.succAbove w) :
    X.toSSetObjEquiv _ (SSet.yonedaEquiv (f j hj)) z =
      X.toSSetObjEquiv _ (SSet.yonedaEquiv (f k hk)) w := by
  cases n with
  | zero =>
    have hjk : j = k := by
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hj
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hk
      exact ha.symm.trans ((congrArg i.succAbove (Subsingleton.elim a b)).trans hb)
    subst k
    have h := stdSimplex_face_map_injective 0 j hzw
    subst w
    rfl
  | succ n =>
    let g (j : Fin (n + 3)) (hj : j ≠ i) :=
      X.toSSetObjEquiv _ (SSet.yonedaEquiv (f j hj))
    have hlt (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k)
        (z w : stdSimplex Real (Fin (n + 2)))
        (hzw : stdSimplex.map j.succAbove z = stdSimplex.map k.succAbove w) :
        g j hj z = g k hk w := by
      obtain ⟨t, htj, htk⟩ := exists_stdSimplex_two_face_preimage n j k hjk z w hzw
      have h := congrArg (fun a : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj X =>
        X.toSSetObjEquiv _ (SSet.yonedaEquiv a) t) (hf j k hj hk hjk)
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, SSet.stdSimplex.yonedaEquiv_δ_comp,
        TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply, htj, htk] at h
      exact h
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · exact hlt j k hj hk hjk z w hzw
    · subst k
      have h := stdSimplex_face_map_injective (n + 1) j hzw
      subst w
      rfl
    · exact (hlt k j hk hj hjk w z hzw.symm).symm

theorem singular_kanComplex (X : TopCat.{u}) :
    SSet.KanComplex (TopCat.toSSet.obj X) := by
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  obtain ⟨F, hF⟩ := exists_stdSimplex_compatible_face_extension n i
    (fun j hj => X.toSSetObjEquiv _ (SSet.yonedaEquiv (f j hj)))
    (fun j k hj hk z w hzw => singular_horn_faces_agree X n i f hf j k hj hk z w hzw)
  refine ⟨SSet.yonedaEquiv.symm ((X.toSSetObjEquiv _).symm F), ?_⟩
  intro j hj
  apply SSet.yonedaEquiv.injective
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply,
    TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply]
  exact hF j hj z

end PoincareConjecture.Proofs.M02.Topology
