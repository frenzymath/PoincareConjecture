import PoincareConjecture.Proofs.M02.Topology.SimplexHornFilling
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Order.Lattice

set_option autoImplicit false

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_stdSimplex_three_face_fold (n : Nat) :
    Exists fun w : C(stdSimplex Real (Fin (n + 2)), stdSimplex Real (Fin (n + 3))) =>
      And (forall z, w z 0 = z 0 - min (z 0) (z 1))
        (And (forall z, w z 1 = 2 * min (z 0) (z 1))
          (And (forall z, w z 2 = z 1 - min (z 0) (z 1))
            (forall z (j : Fin n), w z j.succ.succ.succ = z j.succ.succ))) := by
  let a (z : stdSimplex Real (Fin (n + 2))) : Fin (n + 3) → Real :=
    Fin.cases (z 0 - min (z 0) (z 1))
      (Fin.cases (2 * min (z 0) (z 1))
        (Fin.cases (z 1 - min (z 0) (z 1)) (fun j => z j.succ.succ)))
  have ha (z : stdSimplex Real (Fin (n + 2))) :
      a z ∈ stdSimplex Real (Fin (n + 3)) := by
    constructor
    · intro k
      refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun j => ?_) m) l) k
      · exact sub_nonneg.mpr (min_le_left _ _)
      · exact mul_nonneg zero_le_two (le_min (z.property.1 0) (z.property.1 1))
      · exact sub_nonneg.mpr (min_le_right _ _)
      · exact z.property.1 j.succ.succ
    · have hz := z.property.2
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hz
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      change (z 0 - min (z 0) (z 1)) + (2 * min (z 0) (z 1) +
        ((z 1 - min (z 0) (z 1)) + ∑ j : Fin n, z j.succ.succ)) = 1
      calc
        _ = z 0 + (z 1 + ∑ j : Fin n, z j.succ.succ) := by ring
        _ = 1 := hz
  have hc (k : Fin (n + 2)) : Continuous (fun z : stdSimplex Real (Fin (n + 2)) => z k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hca : Continuous a := by
    apply continuous_pi
    intro k
    refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun j => ?_) m) l) k
    · exact (hc 0).sub ((hc 0).min (hc 1))
    · exact continuous_const.mul ((hc 0).min (hc 1))
    · exact (hc 1).sub ((hc 0).min (hc 1))
    · exact hc j.succ.succ
  exact ⟨⟨fun z => ⟨a z, ha z⟩, hca.subtype_mk ha⟩,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem stdSimplex_three_face_fold_homotopicRel {X : Type u} [TopologicalSpace X]
    (n : Nat)
    (w : C(stdSimplex Real (Fin (n + 2)), stdSimplex Real (Fin (n + 3))))
    (hw0 : forall z, w z 0 = z 0 - min (z 0) (z 1))
    (hw1 : forall z, w z 1 = 2 * min (z 0) (z 1))
    (hw2 : forall z, w z 2 = z 1 - min (z 0) (z 1))
    (hws : forall z (j : Fin n), w z j.succ.succ.succ = z j.succ.succ)
    (F : C(stdSimplex Real (Fin (n + 3)), X)) (x : X)
    (hF : forall j : Fin (n + 3), Ne j 0 -> Ne j 1 -> Ne j 2 ->
      forall z : stdSimplex Real (Fin (n + 2)), F (stdSimplex.map j.succAbove z) = x) :
    ContinuousMap.HomotopicRel
      (F.comp (ContinuousMap.mk (stdSimplex.map (1 : Fin (n + 3)).succAbove)
        (stdSimplex.continuous_map _)))
      (F.comp w)
      (Set.ofPred (fun z : stdSimplex Real (Fin (n + 2)) =>
        Exists fun j : Fin (n + 2) => z j = 0)) := by
  let a : C(stdSimplex Real (Fin (n + 2)), stdSimplex Real (Fin (n + 3))) :=
    ⟨stdSimplex.map (1 : Fin (n + 3)).succAbove, stdSimplex.continuous_map _⟩
  have ha0 (z : stdSimplex Real (Fin (n + 2))) : a z 0 = z 0 := by
    have h := stdSimplex_face_succAbove (n + 1) (1 : Fin (n + 3)) z 0
    rw [Fin.one_succAbove_zero] at h
    exact h
  have ha1 (z : stdSimplex Real (Fin (n + 2))) : a z 1 = 0 :=
    stdSimplex_face_zero (n + 1) 1 z
  have ha2 (z : stdSimplex Real (Fin (n + 2))) : a z 2 = z 1 := by
    have h := stdSimplex_face_succAbove (n + 1) (1 : Fin (n + 3)) z 1
    rw [Fin.one_succAbove_one] at h
    exact h
  have has (z : stdSimplex Real (Fin (n + 2))) (j : Fin n) :
      a z j.succ.succ.succ = z j.succ.succ := by
    have h := stdSimplex_face_succAbove (n + 1) (1 : Fin (n + 3)) z j.succ.succ
    rw [Fin.one_succAbove_succ] at h
    exact h
  have hsame (z : stdSimplex Real (Fin (n + 2))) (hd : min (z 0) (z 1) = 0) :
      a z = w z := by
    apply Subtype.ext
    funext k
    refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun m => Fin.cases ?_ (fun j => ?_) m) l) k
    · change a z 0 = w z 0
      rw [ha0, hw0, hd, sub_zero]
    · change a z 1 = w z 1
      rw [ha1, hw1, hd, mul_zero]
    · change a z 2 = w z 2
      rw [ha2, hw2, hd, sub_zero]
    · exact (has z j).trans (hws z j).symm
  let A : C(stdSimplex Real (Fin (n + 2)), Fin (n + 3) → Real) :=
    ⟨fun z => (a z).val, continuous_subtype_val.comp a.continuous⟩
  let W : C(stdSimplex Real (Fin (n + 2)), Fin (n + 3) → Real) :=
    ⟨fun z => (w z).val, continuous_subtype_val.comp w.continuous⟩
  let H := ContinuousMap.Homotopy.affine A W
  have hm (p : unitInterval × stdSimplex Real (Fin (n + 2))) :
      H p ∈ stdSimplex Real (Fin (n + 3)) :=
    (convex_stdSimplex Real _).lineMap_mem (a p.2).property (w p.2).property p.1.property
  have hstationary (s : unitInterval) (z : stdSimplex Real (Fin (n + 2)))
      (hd : min (z 0) (z 1) = 0) : F ⟨H (s, z), hm (s, z)⟩ = F (a z) := by
    apply congrArg F
    apply Subtype.ext
    change AffineMap.lineMap (a z).val (w z).val (s : Real) = (a z).val
    rw [← hsame z hd, AffineMap.lineMap_same_apply]
  refine ⟨{ toFun := fun p => F ⟨H p, hm p⟩
            continuous_toFun := F.continuous.comp (H.continuous.subtype_mk hm)
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro z
    exact congrArg F (Subtype.ext (H.apply_zero z))
  · intro z
    exact congrArg F (Subtype.ext (H.apply_one z))
  · intro s z hz
    obtain ⟨k, hk⟩ := hz
    cases k using Fin.cases with
    | zero =>
      apply hstationary
      rw [hk]
      exact min_eq_left (z.property.1 1)
    | succ k =>
      cases k using Fin.cases with
      | zero =>
        apply hstationary
        change z 1 = 0 at hk
        rw [hk]
        exact min_eq_right (z.property.1 0)
      | succ j =>
        have hj0 : j.succ.succ.succ ≠ (0 : Fin (n + 3)) := Fin.succ_ne_zero _
        have hj1 : j.succ.succ.succ ≠ (1 : Fin (n + 3)) :=
          fun h => Fin.succ_ne_zero _ (Fin.succ_inj.mp h)
        have hj2 : j.succ.succ.succ ≠ (2 : Fin (n + 3)) :=
          fun h => Fin.succ_ne_zero _ (Fin.succ_inj.mp (Fin.succ_inj.mp h))
        have hzero (v : stdSimplex Real (Fin (n + 3)))
            (hv : v j.succ.succ.succ = 0) : F v = x := by
          obtain ⟨u, rfl⟩ := (stdSimplex_face_range_iff (n + 1) j.succ.succ.succ v).mpr hv
          exact hF _ hj0 hj1 hj2 u
        have haz : a z j.succ.succ.succ = 0 := (has z j).trans hk
        have hwz : w z j.succ.succ.succ = 0 := (hws z j).trans hk
        have hhz : H (s, z) j.succ.succ.succ = 0 := by
          change AffineMap.lineMap (a z).val (w z).val (s : Real) _ = 0
          rw [AffineMap.lineMap_apply_module]
          change (1 - (s : Real)) * a z _ + (s : Real) * w z _ = 0
          rw [haz, hwz, mul_zero, mul_zero, add_zero]
        exact (hzero ⟨H (s, z), hm (s, z)⟩ hhz).trans (hzero (a z) haz).symm

end PoincareConjecture.Proofs.M02.Topology
