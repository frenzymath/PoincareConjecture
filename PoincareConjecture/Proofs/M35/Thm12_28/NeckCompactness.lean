import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetNorm
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch
import PoincareConjecture.Proofs.M09.SpeedDistance

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem axial_tangentNorm_le (N : EpsilonNeck g) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    g.tangentNorm (N.coordinate_map (q, s))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) (0, 1)) ≤
        2 * N.scale := by
  have h := N.metric_comparison.close.component_sq_lt (by norm_num)
    (z := (q, s)) hs (Nat.zero_le _) ![(2 : Fin 3), 2]
  have hc : (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q) = q :=
    (chartAt (EuclideanSpace ℝ (Fin 2)) q).left_inv (mem_chart_source _ q)
  dsimp only at h
  rw [Fin.prod_univ_two] at h
  dsimp [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient,
    roundCylinderGram, EvolvingRoundCylinderMetric, roundCylinderCoordinateBasis] at h
  simp only [one_mul, mul_one] at h
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡 2) (𝓡 2) c.symm (c q)
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.val) (c.symm (c q))
  let B : RoundCylinderSpace → RoundCylinderCoordinates → RoundCylinderCoordinates → ℝ :=
    roundCylinderPullback g N.coordinate_map
  change (N.scale⁻¹ ^ 2 * B (c.symm (c q), s) (D 0, 1) (D 0, 1) -
    (2 * (1 - 0) * inner ℝ (L (D 0)) (L (D 0)) + 1)) ^ 2 < N.epsilon ^ 2 at h
  simp only [map_zero, inner_zero_left, mul_zero, zero_add] at h
  have hpoint : B (c.symm (c q), s) (0, 1) (0, 1) = B (q, s) (0, 1) (0, 1) :=
    congrArg (fun z => B (z, s) (0, 1) (0, 1)) hc
  rw [hpoint] at h
  let A := roundCylinderPullback g N.coordinate_map (q, s) (0, 1) (0, 1)
  have hA : N.scale⁻¹ ^ 2 * A ≤ 2 := by
    change (N.scale⁻¹ ^ 2 * A - 1) ^ 2 < N.epsilon ^ 2 at h
    nlinarith [N.epsilon_pos, N.epsilon_lt_half]
  have hscale : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
  have hcancel : (N.scale⁻¹ ^ 2 * A) * N.scale ^ 2 = A := by
    field_simp [ne_of_gt N.scale_pos]
  have hA' : A ≤ (2 * N.scale) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hA hscale.le
    rw [hcancel] at hmul
    nlinarith
  exact (Real.sqrt_le_sqrt hA').trans_eq
    (Real.sqrt_sq (mul_nonneg (by norm_num) N.scale_pos.le))

theorem axial_curve_velocity (N : EpsilonNeck g) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    curveVelocity (fun r => N.coordinate_map (q, r)) s =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) (0, 1) := by
  have hN := (N.coordinate_map_smooth (q, s) ⟨mem_univ _, hs⟩).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hs⟩)
  have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun r : ℝ => (q, r)) s := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hchain := mfderiv_comp s (hN.mdifferentiableAt (by simp)) hpair
  have hderiv := mfderiv_prodMk (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
    (x := s) (mdifferentiableAt_const (c := q)) mdifferentiableAt_id
  have hvalue : mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun r : ℝ => (q, r)) s (1 : ℝ) = (0, 1) := by
    exact (congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) × ℝ => L 1) hderiv).trans
      (by simp only [mfderiv_const, mfderiv_id]; rfl)
  exact (congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) => L 1) hchain).trans
    (congrArg (fun v : EuclideanSpace ℝ (Fin 2) × ℝ =>
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) v) hvalue)

theorem axial_dist_le [T3Space M] [ConnectedSpace M]
    (N : EpsilonNeck g) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    letI : MetricSpace M := Proofs.M09.selectedMetricSpace g
    dist (N.coordinate_map (q, 0)) (N.coordinate_map (q, s)) ≤ 2 * N.scale * |s| := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun r : ℝ => N.coordinate_map (q, r)) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    N.coordinate_map_smooth.comp (contMDiffOn_const.prodMk contMDiffOn_id)
      (fun _ hr => ⟨mem_univ _, hr⟩)
  have hspeed (r : ℝ) (hr : r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
      g.tangentNorm (N.coordinate_map (q, r))
        (curveVelocity (fun a => N.coordinate_map (q, a)) r) ≤ 2 * N.scale := by
    rw [axial_curve_velocity N q hr]
    exact N.axial_tangentNorm_le q hr
  rcases le_total 0 s with hpos | hneg
  · have hsub : Icc 0 s ⊆ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      intro r hr
      constructor <;> linarith [hr.1, hr.2, hs.2]
    have hbound := Proofs.M09.selectedMetric_dist_le_of_speed_le g
      (fun r => N.coordinate_map (q, r)) 0 s (2 * N.scale) hpos
      (mul_nonneg (by norm_num) N.scale_pos.le)
      ((hγ.mono hsub).of_le (by norm_num)) (fun r hr => hspeed r (hsub hr))
    simpa only [sub_zero, abs_of_nonneg hpos] using hbound
  · have hsub : Icc s 0 ⊆ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      intro r hr
      constructor <;> linarith [hr.1, hr.2, hs.1]
    have hbound := Proofs.M09.selectedMetric_dist_le_of_speed_le g
      (fun r => N.coordinate_map (q, r)) s 0 (2 * N.scale) hneg
      (mul_nonneg (by norm_num) N.scale_pos.le)
      ((hγ.mono hsub).of_le (by norm_num)) (fun r hr => hspeed r (hsub hr))
    simpa only [dist_comm, zero_sub, abs_of_nonpos hneg] using hbound

theorem isCompact_central_sphere_m35 (N : EpsilonNeck g) : IsCompact N.central_sphere := by
  rw [N.central_sphere_eq]
  apply (isCompact_univ.prod isCompact_singleton).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  refine ⟨mem_univ _, ?_⟩
  rw [mem_singleton_iff.mp hz.2]
  exact ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩

theorem isCompact_closure [T3Space M] [ConnectedSpace M]
    (N : EpsilonNeck g) (hcomplete : MetricComplete g) : IsCompact (closure N.carrier) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have : ProperSpace M := Proofs.M09.selectedMetricSpace_proper g hcomplete
  obtain ⟨R, hR⟩ := N.isCompact_central_sphere_m35.isBounded.subset_closedBall N.center
  have hsub : N.carrier ⊆ Metric.closedBall N.center (R + 2 * N.scale * N.epsilon⁻¹) := by
    intro y hy
    let z := N.coordinate_inverse y
    have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem y hy).2
    have hpoint : N.coordinate_map z = y := N.coordinatePartialDiffeomorph.right_inv hy
    have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
      rw [N.central_sphere_eq]
      exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
    have hdist := N.axial_dist_le z.1 hz
    have hscaled : 2 * N.scale * |z.2| ≤ 2 * N.scale * N.epsilon⁻¹ :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
        (mul_nonneg (by norm_num) N.scale_pos.le)
    change dist y N.center ≤ _
    calc
      dist y N.center ≤ dist y (N.coordinate_map (z.1, 0)) +
          dist (N.coordinate_map (z.1, 0)) N.center := dist_triangle _ _ _
      _ ≤ 2 * N.scale * N.epsilon⁻¹ + R := add_le_add
        (by rw [dist_comm, ← hpoint]; exact hdist.trans hscaled) (hR hcentral)
      _ = _ := add_comm _ _
  exact (isCompact_closedBall N.center (R + 2 * N.scale * N.epsilon⁻¹)).of_isClosed_subset
    isClosed_closure (closure_minimal hsub Metric.isClosed_closedBall)

end PoincareConjecture.EpsilonNeck
