import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem normalized_pullback_bilinear_error
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderTangent z) :
    |N.normalized_pullback z v w - EvolvingRoundCylinderMetric 0 z v w| ≤
      N.epsilon * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v) *
        Real.sqrt (EvolvingRoundCylinderMetric 0 z w w) := by
  let : Bundle.RiemannianBundle (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
    ⟨roundCylinderProductMetric.toRiemannianMetric⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  let x : RoundCylinderSpace := (c.symm p.1, p.2)
  let b := roundCylinderChartBasis z.1 p
  let : FiniteDimensional ℝ (RoundCylinderTangent x) := Module.Finite.of_basis b
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map x
  let A : RoundCylinderTangent x →ₗ[ℝ] RoundCylinderTangent x →ₗ[ℝ] ℝ :=
    (N.scale⁻¹ ^ 2) • (g.inner (N.coordinate_map x)).toBilinForm.comp
      D.toLinearMap D.toLinearMap - (roundCylinderProductMetric.inner x).toBilinForm
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) =
      roundCylinderGram 0 c p := by
    ext i j
    simp only [Matrix.of_apply, b, roundCylinderChartBasis_apply]
    exact roundCylinderChartFrame_gram z.1 p i j
  have hcoef (i j : Fin 3) : A (b i) (b j) =
      roundCylinderTensorCoefficient N.normalized_pullback c p i j -
        roundCylinderGram 0 c p i j := by
    change N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map x
      (b i) (b j) - roundCylinderProductMetric.inner x (b i) (b j) = _
    rw [roundCylinderProductMetric_inner]
    simp only [b, roundCylinderChartBasis_apply]
    rfl
  have hA : (∑ i : Fin 2 → Fin 3, ∑ j : Fin 2 → Fin 3,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (b (i 0)) (b (i 1)) * A (b (j 0)) (b (j 1))) ≤ N.epsilon ^ 2 := by
    simp only [hGram, hcoef]
    exact (N.normalized_pullback_zeroth_normSquared_lt hz).le
  have hx : x = z := by
    apply Prod.ext
    · exact c.left_inv (mem_chart_source _ z.1)
    · rfl
  have hbound : ∀ v w : RoundCylinderTangent x,
      |N.normalized_pullback x v w - EvolvingRoundCylinderMetric 0 x v w| ≤
        N.epsilon * Real.sqrt (EvolvingRoundCylinderMetric 0 x v v) *
          Real.sqrt (EvolvingRoundCylinderMetric 0 x w w) := by
    intro v w
    have h := abs_multilinear_apply_le_of_inverse_gram_contraction_le
      (bilinearEvaluationTwoTensor A) b N.epsilon_pos.le hA ![v, w]
    have hnorm (a : RoundCylinderTangent x) :
        Real.sqrt (EvolvingRoundCylinderMetric 0 x a a) = ‖a‖ := by
      rw [← roundCylinderProductMetric_inner]
      exact norm_eq_sqrt_real_inner a |>.symm
    simp only [bilinearEvaluationTwoTensor, MultilinearMap.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.prod_univ_two] at h
    change |N.normalized_pullback x v w - roundCylinderProductMetric.inner x v w| ≤
      N.epsilon * (‖v‖ * ‖w‖) at h
    simpa only [roundCylinderProductMetric_inner, hnorm, mul_assoc] using h
  exact Eq.mp (congrArg (fun y : RoundCylinderSpace =>
    ∀ v w : RoundCylinderTangent y,
      |N.normalized_pullback y v w - EvolvingRoundCylinderMetric 0 y v w| ≤
        N.epsilon * Real.sqrt (EvolvingRoundCylinderMetric 0 y v v) *
          Real.sqrt (EvolvingRoundCylinderMetric 0 y w w)) hx) hbound v w

theorem scaled_model_length_le_two
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z)
    (hv : roundCylinderPullback g N.coordinate_map z v v = 1) :
    N.scale * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v) ≤ 2 := by
  have hnonneg : 0 ≤ EvolvingRoundCylinderMetric 0 z v v := by
    dsimp only [EvolvingRoundCylinderMetric]
    nlinarith [real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 3)
      (fun q : UnitTwoSphere => q.1) z.1 v.1), sq_nonneg v.2]
  have hlow := (N.pullback_metric_bounds hz v).1
  rw [hv] at hlow
  have hprod : 0 ≤ N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z v v :=
    mul_nonneg (sq_nonneg _) hnonneg
  have hsq : (N.scale * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v)) ^ 2 ≤ 4 := by
    rw [mul_pow, Real.sq_sqrt hnonneg]
    nlinarith [N.epsilon_lt_half]
  nlinarith [mul_nonneg N.scale_pos.le (Real.sqrt_nonneg
    (EvolvingRoundCylinderMetric 0 z v v))]

theorem pullback_scaled_axial_pairing_error
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z)
    (hv : roundCylinderPullback g N.coordinate_map z v v = 1) :
    |N.scale⁻¹ * roundCylinderPullback g N.coordinate_map z v (0, 1) -
        N.scale * v.2| ≤ 2 * N.epsilon := by
  have h := N.normalized_pullback_bilinear_error hz v (0, 1)
  have hax : EvolvingRoundCylinderMetric 0 z v (0, 1) = v.2 := by
    simp [EvolvingRoundCylinderMetric]
  have haa : EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) = 1 := by
    simp [EvolvingRoundCylinderMetric]
  rw [hax, haa, Real.sqrt_one, mul_one] at h
  have hscaled : |N.scale * (N.normalized_pullback z v (0, 1) - v.2)| ≤
      N.scale * (N.epsilon * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v)) := by
    simpa only [abs_mul, abs_of_pos N.scale_pos] using
      mul_le_mul_of_nonneg_left h N.scale_pos.le
  have heq : N.scale * (N.normalized_pullback z v (0, 1) - v.2) =
      N.scale⁻¹ * roundCylinderPullback g N.coordinate_map z v (0, 1) -
        N.scale * v.2 := by
    dsimp only [normalized_pullback]
    field_simp [N.scale_pos.ne']
  rw [heq] at hscaled
  exact hscaled.trans (by
    nlinarith [N.scaled_model_length_le_two hz v hv, N.epsilon_pos])

theorem scaled_axial_inner_self_error
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    |g.inner (N.coordinate_map z)
        (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map z (0, 1))
        (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map z (0, 1)) - 1| ≤ N.epsilon := by
  have h := N.normalized_pullback_quadratic_error hz (0, 1)
  have haa : EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) = 1 := by
    simp [EvolvingRoundCylinderMetric]
  rw [haa, mul_one] at h
  simpa only [normalized_pullback, roundCylinderPullback, map_smul,
    smul_apply, smul_eq_mul, pow_two, mul_assoc] using h

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem coordinate_map_mfderiv_inverse_product {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hh := mfderiv_comp x
    ((N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp))
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp))
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_coordinate_inverse hy
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem axial_mvfderiv_eq_coordinate_inverse {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).2 := by
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  change mvfderiv (𝓡 3) (Prod.snd ∘ N.coordinate_inverse) x v = _
  rw [mvfderiv, mfderiv_comp x
    ((contMDiff_snd (n := ∞)).mdifferentiableAt (by simp)) hi, mfderiv_snd]
  rfl

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem ambient_inner_self_nonneg {x : M} (v : TangentSpace (𝓡 3) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

theorem axial_pairing_error {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) (hv : g.tangentNorm x v = 1) :
    |g.inner x v
        (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) (0, 1)) -
      N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
      2 * N.epsilon := by
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v
  have hnorm : g.inner x v v = 1 := by
    have h := congrArg (fun a : ℝ => a ^ 2) hv
    dsimp only [RiemannianMetric.tangentNorm] at h
    rwa [Real.sq_sqrt (ambient_inner_self_nonneg v), one_pow] at h
  have hw : roundCylinderPullback g N.coordinate_map (N.coordinate_inverse x) w w = 1 := by
    dsimp only [roundCylinderPullback, w]
    rw [N.coordinate_map_mfderiv_inverse_product hx v,
      N.coordinate_map_coordinate_inverse hx]
    exact hnorm
  have h := N.pullback_scaled_axial_pairing_error
    (N.coordinate_inverse_mem x hx).2 w hw
  dsimp only [roundCylinderPullback, w] at h
  rw [N.coordinate_map_mfderiv_inverse_product hx v,
    N.coordinate_map_coordinate_inverse hx] at h
  rw [N.axial_mvfderiv_eq_coordinate_inverse hx v]
  simp only [map_smul, smul_eq_mul]
  convert h using 1
  congr 6

theorem scaled_axial_tangentNorm_sq_error {x : M} (hx : x ∈ N.carrier) :
    |(g.tangentNorm x
        (N.scale⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) (0, 1))) ^ 2 - 1| ≤
      N.epsilon := by
  have h := N.scaled_axial_inner_self_error (N.coordinate_inverse_mem x hx).2
  rw [N.coordinate_map_coordinate_inverse hx] at h
  unfold RiemannianMetric.tangentNorm
  rw [Real.sq_sqrt (ambient_inner_self_nonneg _)]
  exact h

theorem tangentNorm_sub_scaled_axial_le_of_velocity
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x)
    (hv : g.tangentNorm x v = 1) {α β : ℝ} (hα : 0 ≤ α)
    (hvel : 1 - β ≤
      N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v)
    (hquality : 2 * β + 5 * N.epsilon ≤ α ^ 2) :
    let a : TangentSpace (𝓡 3) x := N.scale⁻¹ •
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (N.coordinate_inverse x) (0, 1)
    g.tangentNorm x (v - a) ≤ α := by
  let a : TangentSpace (𝓡 3) x := N.scale⁻¹ •
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      N.coordinate_map (N.coordinate_inverse x) (0, 1)
  have hvv : g.inner x v v = 1 := by
    have h := congrArg (fun a : ℝ => a ^ 2) hv
    dsimp only [RiemannianMetric.tangentNorm] at h
    rwa [Real.sq_sqrt (ambient_inner_self_nonneg v), one_pow] at h
  have haa : g.inner x a a ≤ 1 + N.epsilon := by
    have h := N.scaled_axial_tangentNorm_sq_error hx
    change |g.tangentNorm x a ^ 2 - 1| ≤ N.epsilon at h
    unfold RiemannianMetric.tangentNorm at h
    rw [Real.sq_sqrt (ambient_inner_self_nonneg a)] at h
    have hh := (abs_le.mp h).2
    linarith
  have hva : 1 - β - 2 * N.epsilon ≤ g.inner x v a := by
    have h := (abs_le.mp (N.axial_pairing_error hx v hv)).1
    change -(2 * N.epsilon) ≤ g.inner x v a -
      N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v at h
    linarith
  have hsq : g.inner x (v - a) (v - a) ≤ α ^ 2 := by
    simp only [map_sub, sub_apply]
    rw [g.symm x a v]
    nlinarith
  exact (Real.sqrt_le_iff).mpr ⟨hα, hsq⟩

theorem tangentNorm_sub_scaled_axial_lt_of_velocity
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x)
    (hv : g.tangentNorm x v = 1) {α β : ℝ} (hα : 0 < α)
    (hvel : 1 - β ≤
      N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v)
    (hquality : 2 * β + 5 * N.epsilon < α ^ 2) :
    let a : TangentSpace (𝓡 3) x := N.scale⁻¹ •
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.coordinate_map (N.coordinate_inverse x) (0, 1)
    g.tangentNorm x (v - a) < α := by
  have hbudget : 2 * β + 5 * N.epsilon ≤
      Real.sqrt (max 0 (2 * β + 5 * N.epsilon)) ^ 2 := by
    rw [Real.sq_sqrt (le_max_left _ _)]
    exact le_max_right _ _
  exact (N.tangentNorm_sub_scaled_axial_le_of_velocity hx v hv
    (Real.sqrt_nonneg _) hvel hbudget).trans_lt
      ((Real.sqrt_lt' hα).mpr (max_lt (sq_pos_of_pos hα) hquality))

end PoincareConjecture.EpsilonNeck
