import PoincareConjecture.Proofs.M09.PathPrimitive
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp









set_option autoImplicit false

open scoped Topology intervalIntegral
open Set Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def pathRescale (c : ℝ) (v : C(Set.Icc (-1 : ℝ) 1, E)) :
    C(Set.Icc (-1 : ℝ) 1, E) :=
  v.comp ⟨fun r ↦ symmetricTimeProjection (c * (r : ℝ)),
    symmetricTimeProjection.continuous.comp (continuous_const.mul continuous_subtype_val)⟩

@[simp] theorem pathRescale_apply (c : ℝ) (v : C(Set.Icc (-1 : ℝ) 1, E))
    (r : Set.Icc (-1 : ℝ) 1) :
    pathRescale c v r = v (symmetricTimeProjection (c * (r : ℝ))) := rfl

theorem pathRescale_norm_sub_const_le (c : ℝ) (v : C(Set.Icc (-1 : ℝ) 1, E)) (x : E) :
    ‖pathRescale c v - ContinuousMap.const _ x‖ ≤ ‖v - ContinuousMap.const _ x‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro r
  exact (v - ContinuousMap.const _ x).norm_coe_le_norm
    (symmetricTimeProjection (c * (r : ℝ)))

variable [CompleteSpace E]

theorem picard_path_at_zero (f : C(E, E)) (x : E) (a : ℝ)
    (v : C(Set.Icc (-1 : ℝ) 1, E))
    (hv : v = ContinuousMap.const _ x + a • pathPrimitive (f.comp v)) :
    v ⟨0, by norm_num⟩ = x := by
  have h := congrArg (fun w : C(Set.Icc (-1 : ℝ) 1, E) ↦ w ⟨0, by norm_num⟩) hv
  simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
    ContinuousMap.smul_apply, pathPrimitive_at_zero, smul_zero, add_zero] using h

theorem picard_path_hasDerivAt (f : C(E, E)) (x : E) (a : ℝ)
    (v : C(Set.Icc (-1 : ℝ) 1, E))
    (hv : v = ContinuousMap.const _ x + a • pathPrimitive (f.comp v))
    (r : ℝ) (hr : r ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s : ℝ ↦ v (symmetricTimeProjection s))
      (a • f (v (symmetricTimeProjection r))) r := by
  have hd : HasDerivAt
      (fun t : ℝ ↦ x + a • ∫ s in 0..t, (f.comp v) (symmetricTimeProjection s))
      (a • f (v (symmetricTimeProjection r))) r :=
    (HasDerivAt.const_smul a (pathPrimitive_hasDerivAt (f.comp v) r hr)).const_add x
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  have hsI : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  rw [symmetricTimeProjection_of_mem hsI]
  have h := congrArg (fun w : C(Set.Icc (-1 : ℝ) 1, E) ↦ w ⟨s, hsI⟩) hv
  exact h

theorem pathRescale_picard (f : C(E, E)) (x : E) (a c : ℝ)
    (v : C(Set.Icc (-1 : ℝ) 1, E))
    (hv : v = ContinuousMap.const _ x + a • pathPrimitive (f.comp v)) (hc : |c| ≤ 1) :
    pathRescale c v = ContinuousMap.const _ x +
      (a * c) • pathPrimitive (f.comp (pathRescale c v)) := by
  ext r
  have hcr : c * (r : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_mul]
    exact (mul_le_mul hc (abs_le.mpr r.property) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have hInt : (∫ s in 0..(r : ℝ), f (v (symmetricTimeProjection (c * s)))) =
      ∫ s in 0..(r : ℝ), (f.comp (pathRescale c v)) (symmetricTimeProjection s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Set.Icc (-1 : ℝ) 1 :=
      Set.uIcc_subset_Icc (by norm_num) r.property hs
    change f (v (symmetricTimeProjection (c * s))) =
      (f.comp (pathRescale c v)) (symmetricTimeProjection s)
    rw [symmetricTimeProjection_of_mem hsI]
    rfl
  have h := congrArg (fun w : C(Set.Icc (-1 : ℝ) 1, E) ↦
    w ⟨c * (r : ℝ), hcr⟩) hv
  change v ⟨c * (r : ℝ), hcr⟩ =
    x + a • ∫ s in 0..c * (r : ℝ), f (v (symmetricTimeProjection s)) at h
  rw [pathRescale_apply, symmetricTimeProjection_of_mem hcr, h]
  change x + a • (∫ s in 0..c * (r : ℝ), f (v (symmetricTimeProjection s))) =
    x + (a * c) • ∫ s in 0..(r : ℝ),
      (f.comp (pathRescale c v)) (symmetricTimeProjection s)
  rw [← hInt, mul_smul]
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (fun s ↦ f (v (symmetricTimeProjection s))) (a := 0) (b := (r : ℝ)) c
  rw [mul_zero] at hsub
  rw [hsub]

end PoincareConjecture.Proofs.M09
