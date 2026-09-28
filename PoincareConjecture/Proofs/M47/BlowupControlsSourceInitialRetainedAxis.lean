import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoining
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47



theorem source_initial_retained_axis_distance
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants}
    {g : RiemannianMetric 3 M} {I : MetricSurgeryInput K g}
    (R : MetricSurgeryResult g0 I) (q : UnitTwoSphere)
    {a : ℝ} (ha : a ∈ Ioo (-I.neck.epsilon⁻¹) 0) :
    R.metric.edist (R.collapse (I.neck.coordinate_map (q, a)))
        (R.collapse (I.neck.coordinate_map (q, 0))) ≤
      ENNReal.ofReal (I.neck.scale * Real.sqrt (1 + I.neck.epsilon) * |a|) := by
  let N := I.neck
  let J := Ioo (-N.epsilon⁻¹) (min 1 N.epsilon⁻¹)
  let oldCurve : ℝ → M := fun s => N.coordinate_map (q, s)
  let curve := R.collapse ∘ oldCurve
  have hJ : IsOpen J := isOpen_Ioo
  have hdomain (s : ℝ) (hs : s ∈ J) : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩
  have hregion (s : ℝ) (hs : s ∈ J) : oldCurve s ∈ N.region (-N.epsilon⁻¹) 1 := by
    refine ⟨M36.neck_coordinate_mem N (q, s) ⟨mem_univ _, hdomain s hs⟩, ?_⟩
    change (N.coordinate_inverse (N.coordinate_map (q, s))).2 ∈ Ioo (-N.epsilon⁻¹) 1
    rw [M36.neck_inverse_coordinate N (q, s) ⟨mem_univ _, hdomain s hs⟩]
    exact ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
  have hold : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ oldCurve J :=
    N.coordinate_map_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun s hs => ⟨mem_univ _, hdomain s hs⟩)
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ curve J :=
    R.retained_smooth.comp hold hregion
  have hsub : Icc a 0 ⊆ J := by
    intro s hs
    refine ⟨ha.1.trans_le hs.1, hs.2.trans_lt ?_⟩
    exact lt_min (by norm_num) (inv_pos.mpr N.epsilon_pos)
  have hspeed (s : ℝ) (hs : s ∈ Icc a 0) :
      R.metric.tangentNorm (curve s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) curve s 1) ≤
        N.scale * Real.sqrt (1 + N.epsilon) := by
    have hsJ := hsub hs
    have hcoord := M36.neck_coordinate_contMDiffAt N
      (z := (q, s)) ⟨mem_univ _, hdomain s hsJ⟩
    have holdAt := (hold s hsJ).contMDiffAt (hJ.mem_nhds hsJ)
    have hcollapse := (R.retained_smooth (oldCurve s) (hregion s hsJ)).contMDiffAt
      ((M36.neck_region_isOpen N _ _).mem_nhds (hregion s hsJ))
    have hretained : oldCurve s ∈ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere := by
      apply (M36.neck_retained_iff N).mpr
      refine ⟨(hregion s hsJ).1, ?_⟩
      change (N.coordinate_inverse (N.coordinate_map (q, s))).2 ≤ 0
      rw [M36.neck_inverse_coordinate N (q, s) ⟨mem_univ _, hdomain s hsJ⟩]
      exact hs.2
    have hderivative : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) oldCurve s 1 =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) (0, 1) := by
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
        (N.coordinate_map ∘ fun t : ℝ => (q, t)) s 1 = _
      rw [mfderiv_comp_apply s (hcoord.mdifferentiableAt (by simp))
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)]
      simp only [mfderiv_prod_right]
      rfl
    have hinner : R.metric.inner (curve s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) curve s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) curve s 1) ≤
          (N.scale * Real.sqrt (1 + N.epsilon)) ^ 2 := by
      have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) curve s 1 =
          mfderiv (𝓡 3) (𝓡 3) R.collapse (oldCurve s)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) oldCurve s 1) :=
        mfderiv_comp_apply s (hcollapse.mdifferentiableAt (by simp))
          (holdAt.mdifferentiableAt (by simp)) (1 : ℝ)
      rw [hcomp]
      dsimp only [curve, Function.comp_apply]
      rw [R.retained_metric (oldCurve s) hretained,
        hderivative, mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos])]
      simpa only [oldCurve, roundCylinderPullback, EvolvingRoundCylinderMetric,
        Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric_inner,
        RiemannianMetric.euclideanMetric_inner,
        map_zero, inner_zero_left, mul_zero, zero_mul, zero_add, one_mul, mul_one,
        sub_zero, mul_comm] using (N.pullback_metric_bounds (hdomain s hsJ) (0, 1)).2
    exact (Real.sqrt_le_sqrt hinner).trans_eq
      (Real.sqrt_sq (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)))
  have hdist := R.metric.edist_le_of_tangentNorm_le ha.2.le hJ hsub hcurve
    (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)) hspeed
  simpa only [curve, Function.comp_apply, oldCurve, zero_sub, abs_of_neg ha.2] using hdist

end PoincareConjecture.M47
