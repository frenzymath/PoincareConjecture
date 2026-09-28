import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.MetricSpace.Contracting









set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem exists_unique_normal_fiber_point
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    (T : Submodule Real E) [T.HasOrthogonalProjection]
    (p : E) (r R : Real) (hr : 0 < r) (hrR : r ≤ R)
    (f : T → E) (kappa : NNReal) (hkappa : kappa < 1)
    (herr : ∀ v : T, ‖v‖ ≤ R → ‖f v - p - (v : E)‖ ≤ r)
    (hlip : LipschitzOnWith kappa
      (fun v : T => f v - p - (v : E)) (closedBall 0 R)) :
    ∃ v : T, ‖v‖ ≤ r ∧ T.orthogonalProjectionOnto (f v - p) = 0 ∧
      ∀ w : T, ‖w‖ ≤ R → T.orthogonalProjectionOnto (f w - p) = 0 → w = v := by
  let error (v : T) : E := f v - p - (v : E)
  let S : Set T := closedBall 0 r
  have hproj (v : T) : T.orthogonalProjectionOnto (error v) =
      T.orthogonalProjectionOnto (f v - p) - v := by
    simp only [error, map_sub, T.orthogonalProjectionOnto_mem_subspace_eq_self]
  have hsource (v : S) : ‖(v : T)‖ ≤ R :=
    (mem_closedBall_zero_iff.mp v.property).trans hrR
  let H : S → S := fun v => ⟨-T.orthogonalProjectionOnto (error v), by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_neg]
    exact (T.norm_orthogonalProjectionOnto_apply_le _).trans (herr v (hsource v))⟩
  have hH : ContractingWith kappa H := by
    refine ⟨hkappa, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    change dist (-T.orthogonalProjectionOnto (error v))
      (-T.orthogonalProjectionOnto (error w)) ≤ (kappa : Real) * dist (v : T) (w : T)
    rw [dist_neg_neg]
    calc
      dist (T.orthogonalProjectionOnto (error v))
          (T.orthogonalProjectionOnto (error w)) ≤ dist (error v) (error w) := by
        rw [dist_eq_norm, ← map_sub, dist_eq_norm]
        exact T.norm_orthogonalProjectionOnto_apply_le _
      _ ≤ (kappa : Real) * dist (v : T) (w : T) :=
        hlip.dist_le_mul v (mem_closedBall_zero_iff.mpr (hsource v))
          w (mem_closedBall_zero_iff.mpr (hsource w))
  let : CompleteSpace S := isClosed_closedBall.isComplete.completeSpace_coe
  let v0 : S := ⟨0, mem_closedBall_self hr.le⟩
  obtain ⟨v, hv, _⟩ := hH.exists_fixedPoint v0 (edist_ne_top _ _)
  have hfixed : -T.orthogonalProjectionOnto (error v) = (v : T) :=
    congrArg Subtype.val hv
  have heq : T.orthogonalProjectionOnto (f (v : T) - p) = 0 := by
    have h : T.orthogonalProjectionOnto (error v) = -(v : T) :=
      (neg_eq_iff_eq_neg).mp hfixed
    rw [hproj] at h
    exact sub_eq_neg_self.mp h
  refine ⟨v, mem_closedBall_zero_iff.mp v.property, heq, ?_⟩
  intro w hw hweq
  have hwp : -T.orthogonalProjectionOnto (error w) = w := by
    rw [hproj, hweq, zero_sub, neg_neg]
  have hwr : ‖w‖ ≤ r := by
    rw [← hwp, norm_neg]
    exact (T.norm_orthogonalProjectionOnto_apply_le _).trans (herr w hw)
  let w' : S := ⟨w, mem_closedBall_zero_iff.mpr hwr⟩
  have hwfix : Function.IsFixedPt H w' := Subtype.ext hwp
  exact congrArg Subtype.val (hH.fixedPoint_unique' hwfix hv)

end PoincareConjecture.Proofs.M02.Topology
