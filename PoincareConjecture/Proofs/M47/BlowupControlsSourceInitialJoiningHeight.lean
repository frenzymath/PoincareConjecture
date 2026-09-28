import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialInverse
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoining
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem source_initial_joining_height_derivative
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda : ℝ}
    {J : Set ℝ} {V : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J) (hbase : ∀ y ∈ V, HEq (e.forward 0 hzero y) y)
    (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000) (hLambda : 0 < Lambda)
    (hbudget : 1 ≤ (1 - ((F.event t hT).necks i).neck.epsilon) * Lambda ^ 2)
    {U : Set StandardCapSpace} (hU : IsOpen U)
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {x : StandardCapSpace} (hx : x ∈ U) (w : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (fun z => (((F.event t hT).necks i).neck.coordinate_inverse
      (sourceInitialOldMap initial z)).2) x w| ≤
        ((101 / 100 : ℝ) * Lambda) * F.standard_initial.metric.tangentNorm x w := by
  let old := ((F.event t hT).necks i).neck
  let f := sourceInitialOldMap initial
  let height : (F.event t hT).terminal.carrier → ℝ := fun y => (old.coordinate_inverse y).2
  have hh : 0 < F.parameters.h t := (F.event t hT).neck_scale i ▸ old.scale_pos
  let gQ : RiemannianMetric 3 (F.slice t).carrier :=
    M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
    (sq_pos_of_pos (inv_pos.mpr hh))
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = V :=
    comparison.choose_spec.2.2.2.1
  have hV : IsOpen V := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hxV : initial.chart x ∈ V := himage ▸ mem_image_of_mem initial.chart (hsource hx)
  have hcoeff : capComparisonCoefficients e initial.chart 0 hzero x w w =
      gQ.inner (initial.chart x) (mfderiv (𝓡 3) (𝓡 3) initial.chart x w)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart x w) := by
    rw [capComparisonCoefficients_apply,
      surgeryCylinder_pullbackInner_zero hV e hzero hbase hxV]
    rfl
  have hupper := (capComparison_metric_bounds e initial.chart comparison heta
    0 hzero (hsource hx) w).2
  have hmodel : S.metric 0 = F.standard_initial.metric := S.base.initial_metric
  rw [hmodel, hcoeff] at hupper
  have hnonneg : 0 ≤ F.standard_initial.metric.inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (F.standard_initial.metric.pos x w hw).le
  have hnorm : gQ.tangentNorm (initial.chart x)
      (mfderiv (𝓡 3) (𝓡 3) initial.chart x w) ≤
        (101 / 100 : ℝ) * F.standard_initial.metric.tangentNorm x w := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
    rw [RiemannianMetric.tangentNorm, mul_pow, Real.sq_sqrt hnonneg]
    exact hupper.trans (mul_le_mul_of_nonneg_right
      (by norm_num; linarith only [hetaSmall]) hnonneg)
  change RiemannianMetric.tangentNorm
    (M13.scaleSmoothMetric (F.metric t) ((F.parameters.h t)⁻¹ ^ 2)
      (sq_pos_of_pos (inv_pos.mpr hh))) _ _ ≤ _ at hnorm
  rw [M13.scaleSmoothMetric_tangentNorm, Real.sqrt_sq (inv_pos.mpr hh).le] at hnorm
  have hphysical : (F.metric t).tangentNorm (initial.chart x)
      (mfderiv (𝓡 3) (𝓡 3) initial.chart x w) ≤
        F.parameters.h t * ((101 / 100 : ℝ) * F.standard_initial.metric.tangentNorm x w) := by
    calc
      _ = F.parameters.h t * ((F.parameters.h t)⁻¹ *
          (F.metric t).tangentNorm (initial.chart x)
            (mfderiv (𝓡 3) (𝓡 3) initial.chart x w)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hh.le
  obtain ⟨hf, _, hnegative⟩ := source_initial_old_map_properties initial hsource havoid
  have hy := hnegative hx
  have hfAt := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hheight : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ height (f x) :=
    ((old.coordinate_inverse_smooth (f x) hy.1).contMDiffAt
      (old.carrier_open.mem_nhds hy.1)).snd
  have hchain : mvfderiv (𝓡 3) (fun z => height (f z)) x w =
      mvfderiv (𝓡 3) height (f x) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
    change mvfderiv (𝓡 3) (height ∘ f) x w = _
    rw [mvfderiv_comp x (hheight.mdifferentiableAt (by simp))
      (hfAt.mdifferentiableAt (by simp))]
    rfl
  have haxial := old.axial_mvfderiv_bound hy.1 (mfderiv (𝓡 3) (𝓡 3) f x w)
  have hmetric := congrArg Real.sqrt (source_initial_old_map_metric
    initial hU hsource havoid hx w w)
  change (F.event t hT).limit_metric.tangentNorm (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x w) =
    (F.metric t).tangentNorm (initial.chart x)
      (mfderiv (𝓡 3) (𝓡 3) initial.chart x w) at hmetric
  rw [hmetric, (F.event t hT).neck_scale i] at haxial
  have hscaled : Real.sqrt (1 - old.epsilon) *
      |mvfderiv (𝓡 3) height (f x) (mfderiv (𝓡 3) (𝓡 3) f x w)| ≤
        (101 / 100 : ℝ) * F.standard_initial.metric.tangentNorm x w := by
    apply (mul_le_mul_iff_right₀ hh).mp
    simpa only [mul_assoc] using haxial.trans hphysical
  have hfactor : 1 ≤ Lambda * Real.sqrt (1 - old.epsilon) := by
    have hsquare : 1 ≤ (Lambda * Real.sqrt (1 - old.epsilon)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith only [old.epsilon_lt_half])]
      nlinarith only [hbudget]
    nlinarith only [hsquare, mul_nonneg hLambda.le (Real.sqrt_nonneg (1 - old.epsilon))]
  change |mvfderiv (𝓡 3) (fun z => height (f z)) x w| ≤ _
  rw [hchain]
  calc
    _ ≤ (Lambda * Real.sqrt (1 - old.epsilon)) *
        |mvfderiv (𝓡 3) height (f x) (mfderiv (𝓡 3) (𝓡 3) f x w)| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)
    _ = Lambda * (Real.sqrt (1 - old.epsilon) *
        |mvfderiv (𝓡 3) height (f x) (mfderiv (𝓡 3) (𝓡 3) f x w)|) := by ring
    _ ≤ Lambda * ((101 / 100 : ℝ) * F.standard_initial.metric.tangentNorm x w) :=
      mul_le_mul_of_nonneg_left hscaled hLambda.le
    _ = _ := by ring

end PoincareConjecture.M47
