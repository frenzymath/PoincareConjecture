import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.AxialCoordinate

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in

theorem roundCylinderClose_scaled_pullback_bilinear_error
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε Q : ℝ} (hε : 0 ≤ ε)
    (hclose : RoundCylinderClose ε 0 (fun z v w => Q * roundCylinderPullback g f z v w))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v w : RoundCylinderTangent z) :
    |Q * roundCylinderPullback g f z v w - EvolvingRoundCylinderMetric 0 z v w| ≤
      ε * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v) *
        Real.sqrt (EvolvingRoundCylinderMetric 0 z w w) := by
  let : Bundle.RiemannianBundle (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
    ⟨roundCylinderProductMetric.toRiemannianMetric⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  let x : RoundCylinderSpace := (c.symm p.1, p.2)
  let b := roundCylinderChartBasis z.1 p
  let : FiniteDimensional ℝ (RoundCylinderTangent x) := Module.Finite.of_basis b
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f x
  let A : RoundCylinderTangent x →ₗ[ℝ] RoundCylinderTangent x →ₗ[ℝ] ℝ :=
    Q • (g.inner (f x)).toBilinForm.comp D.toLinearMap D.toLinearMap -
      (roundCylinderProductMetric.inner x).toBilinForm
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) = roundCylinderGram 0 c p := by
    ext i j
    simp only [Matrix.of_apply, b, roundCylinderChartBasis_apply]
    exact roundCylinderChartFrame_gram z.1 p i j
  have hcoef (i j : Fin 3) : A (b i) (b j) =
      roundCylinderTensorCoefficient (fun z v w => Q * roundCylinderPullback g f z v w)
        c p i j - roundCylinderGram 0 c p i j := by
    change Q * roundCylinderPullback g f x (b i) (b j) -
      roundCylinderProductMetric.inner x (b i) (b j) = _
    rw [roundCylinderProductMetric_inner]
    simp only [b, roundCylinderChartBasis_apply]
    rfl
  have hA : (∑ i : Fin 2 → Fin 3, ∑ j : Fin 2 → Fin 3,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (b (i 0)) (b (i 1)) * A (b (j 0)) (b (j 1))) ≤ ε ^ 2 := by
    simp only [hGram, hcoef]
    obtain ⟨_, bound, hbound, hjet⟩ := hclose
    apply le_of_lt
    apply lt_of_le_of_lt ?_ ((hjet z hz).trans_lt hbound)
    change roundCylinderTensorNormSquared 0 c p
      (roundCylinderIteratedDerivative 0 c
        (fun z v w => Q * roundCylinderPullback g f z v w) 0 p) ≤ _
    dsimp only [roundCylinderJetErrorSquared]
    apply Finset.single_le_sum (f := fun k =>
      roundCylinderTensorNormSquared 0 c p
        (roundCylinderIteratedDerivative 0 c
          (fun z v w => Q * roundCylinderPullback g f z v w) k p))
    · intro k _
      exact roundCylinderTensorNormSquared_nonneg z.1 _ _
    · simp
  have hx : x = z := Prod.ext (c.left_inv (mem_chart_source _ z.1)) rfl
  have hbound : ∀ v w : RoundCylinderTangent x,
      |Q * roundCylinderPullback g f x v w - EvolvingRoundCylinderMetric 0 x v w| ≤
        ε * Real.sqrt (EvolvingRoundCylinderMetric 0 x v v) *
          Real.sqrt (EvolvingRoundCylinderMetric 0 x w w) := by
    intro v w
    have h := abs_multilinear_apply_le_of_inverse_gram_contraction_le
      (bilinearEvaluationTwoTensor A) b hε hA ![v, w]
    have hnorm (a : RoundCylinderTangent x) :
        Real.sqrt (EvolvingRoundCylinderMetric 0 x a a) = ‖a‖ := by
      rw [← roundCylinderProductMetric_inner]
      exact (norm_eq_sqrt_real_inner a).symm
    simp only [bilinearEvaluationTwoTensor, MultilinearMap.coe_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at h
    change |Q * roundCylinderPullback g f x v w - roundCylinderProductMetric.inner x v w| ≤
      ε * (‖v‖ * ‖w‖) at h
    simpa only [roundCylinderProductMetric_inner, hnorm, mul_assoc] using h
  exact Eq.mp (congrArg (fun y : RoundCylinderSpace =>
    ∀ v w : RoundCylinderTangent y,
      |Q * roundCylinderPullback g f y v w - EvolvingRoundCylinderMetric 0 y v w| ≤
        ε * Real.sqrt (EvolvingRoundCylinderMetric 0 y v v) *
          Real.sqrt (EvolvingRoundCylinderMetric 0 y w w)) hx) hbound v w

theorem cylinderCover_scaled_model_length_le_two
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hr : 0 < r)
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : RoundCylinderTangent z) (hv : roundCylinderPullback g f z v v = 1) :
    r * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v) ≤ 2 := by
  have hnonneg : 0 ≤ EvolvingRoundCylinderMetric 0 z v v := by
    rw [← roundCylinderProductMetric_inner]
    by_cases hv : v = 0
    · simp [hv]
    · exact (roundCylinderProductMetric.pos z v hv).le
  have hlow := (abs_le.mp (roundCylinderClose_scaled_pullback_quadratic_error
    g f hε hclose hz v)).1
  rw [hv, mul_one] at hlow
  have hlow' := mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
  have hcancel : r ^ 2 * r⁻¹ ^ 2 = 1 := by field_simp
  have hsq : (r * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v)) ^ 2 ≤ 4 := by
    rw [mul_pow, Real.sq_sqrt hnonneg]
    nlinarith [mul_nonneg (sq_nonneg r) hnonneg]
  nlinarith [mul_nonneg hr.le (Real.sqrt_nonneg (EvolvingRoundCylinderMetric 0 z v v))]

theorem cylinderCover_pullback_scaled_axial_pairing_error
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    {ε r : ℝ} (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hr : 0 < r)
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w))
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : RoundCylinderTangent z) (hv : roundCylinderPullback g f z v v = 1) :
    |r⁻¹ * roundCylinderPullback g f z v (0, 1) - r * v.2| ≤ 2 * ε := by
  have h := roundCylinderClose_scaled_pullback_bilinear_error g f hε hclose hz v (0, 1)
  have hax : EvolvingRoundCylinderMetric 0 z v (0, 1) = v.2 := by
    simp [EvolvingRoundCylinderMetric]
  have haa : EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) = 1 := by
    simp [EvolvingRoundCylinderMetric]
  rw [hax, haa, Real.sqrt_one, mul_one] at h
  have hscaled : |r * (r⁻¹ ^ 2 * roundCylinderPullback g f z v (0, 1) - v.2)| ≤
      r * (ε * Real.sqrt (EvolvingRoundCylinderMetric 0 z v v)) := by
    simpa only [abs_mul, abs_of_pos hr] using mul_le_mul_of_nonneg_left h hr.le
  have heq : r * (r⁻¹ ^ 2 * roundCylinderPullback g f z v (0, 1) - v.2) =
      r⁻¹ * roundCylinderPullback g f z v (0, 1) - r * v.2 := by
    field_simp [hr.ne']
  rw [heq] at hscaled
  exact hscaled.trans (by
    nlinarith [cylinderCover_scaled_model_length_le_two g f hε hεhalf hr hclose hz v hv])

theorem cylinderCover_tangentNorm_sub_scaled_axial_le_of_velocity
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε r : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hr : 0 < r)
    (hf : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0
      (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w))
    {a : M → ℝ}
    (ha : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)))
    (hvalue : ∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : TangentSpace (𝓡 3) (f z)) (hv : g.tangentNorm (f z) v = 1)
    {α β : ℝ} (hα : 0 ≤ α)
    (hvel : 1 - β ≤ r * mvfderiv (𝓡 3) a (f z) v)
    (hquality : 2 * β + 5 * ε ≤ α ^ 2) :
    g.tangentNorm (f z)
      (v - r⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z (0, 1)) ≤ α := by
  let axial : TangentSpace (𝓡 3) (f z) :=
    r⁻¹ • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z (0, 1)
  have hvnonneg : 0 ≤ g.inner (f z) v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos (f z) v hv).le
  have hvv : g.inner (f z) v v = 1 := by
    have h := congrArg (fun t : ℝ => t ^ 2) hv
    dsimp only [RiemannianMetric.tangentNorm] at h
    rwa [Real.sq_sqrt hvnonneg, one_pow] at h
  obtain ⟨w, hw⟩ := ((hf ⟨z, ⟨mem_univ _, hz⟩⟩).mfderivToContinuousLinearEquiv
    (by simp)).surjective v
  change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z w = v at hw
  have hwpull : roundCylinderPullback g f z w w = 1 := by
    dsimp only [roundCylinderPullback]
    rw [hw]
    exact hvv
  have hwax : mvfderiv (𝓡 3) a (f z) v = w.2 := by
    rw [← hw]
    exact cylinderCover_axialCoordinate_mfderiv hf ha hvalue ⟨mem_univ _, hz⟩ w
  have hpair := cylinderCover_pullback_scaled_axial_pairing_error g f hε hεhalf hr
    hclose hz w hwpull
  dsimp only [roundCylinderPullback] at hpair
  rw [hw] at hpair
  have hpair' : |g.inner (f z) v axial - r * mvfderiv (𝓡 3) a (f z) v| ≤ 2 * ε := by
    rw [hwax]
    simpa only [axial, map_smul, smul_eq_mul] using hpair
  have haa : g.inner (f z) axial axial ≤ 1 + ε := by
    have h := roundCylinderClose_scaled_pullback_quadratic_error g f hε hclose hz (0, 1)
    have hmodel : EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) = 1 := by
      simp [EvolvingRoundCylinderMetric]
    rw [hmodel, mul_one] at h
    have h' : |g.inner (f z) axial axial - 1| ≤ ε := by
      simpa only [axial, roundCylinderPullback, map_smul, smul_apply, smul_eq_mul,
        pow_two, mul_assoc] using h
    linarith [(abs_le.mp h').2]
  have hva : 1 - β - 2 * ε ≤ g.inner (f z) v axial := by
    linarith [(abs_le.mp hpair').1]
  have hsq : g.inner (f z) (v - axial) (v - axial) ≤ α ^ 2 := by
    simp only [map_sub, sub_apply]
    rw [g.symm (f z) axial v]
    nlinarith
  exact (Real.sqrt_le_iff).mpr ⟨hα, hsq⟩

end PoincareConjecture
