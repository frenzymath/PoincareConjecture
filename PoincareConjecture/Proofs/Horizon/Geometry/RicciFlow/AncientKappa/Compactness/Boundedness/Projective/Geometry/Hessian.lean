import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.Reparametrization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.LocalChart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.NeckChart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.Estimate









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CylinderCover



theorem exists_axial_hessian_bound :
    ∃ K : ℝ, ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
      (f : RoundCylinderSpace → M) {ε r : ℝ}, 0 < ε → ε < 1 / 2 → 0 < r →
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
        (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) →
      RoundCylinderClose ε 0 (fun z v w => r⁻¹ ^ 2 * roundCylinderPullback g f z v w) →
      ∀ a : M → ℝ,
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (f '' (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹)) →
      (∀ z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹, a (f z) = z.2) →
      ∀ {z : RoundCylinderSpace}, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      ∀ v : TangentSpace (𝓡 3) (f z), g.tangentNorm (f z) v = 1 →
      |D.hessian a (f z) v v| ≤ K * ε / r ^ 2 := by
  let e : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (RiemannianMetric.lineModelEquiv 2).trans EpsilonNeck.finSuccModelEquiv
  let ell : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp e.symm.toContinuousLinearMap
  let A : ℝ := (2 * (max 1 ‖e.toContinuousLinearMap‖) ^ 2)⁻¹
  let d : ℝ := 216 * ‖e.symm.toContinuousLinearMap‖ ^ 3
  have hAmax : 0 < max 1 ‖e.toContinuousLinearMap‖ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hA : 0 < A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨3 * ‖ell‖ * d / (2 * A ^ 2), ?_⟩
  intro M _ _ _ _ _ _ _ g D f ε r hε hεhalf hr hf hclose a ha havalue z hz u hu
  rcases z with ⟨q, s⟩
  have hεone : ε ≤ 1 := hεhalf.le.trans (by norm_num)
  let p := e (0, s)
  obtain ⟨B, hp, hBs, hBi, hchart⟩ := exists_centered_localChart hf q hz e
  have hpx : B p = f (q, s) := by
    rw [hchart]
    simp only [Function.comp_apply, p, e.symm_apply_apply, centeredParametrization,
      sphere_chart_symm_zero]
  have hB : B.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨hBs.mdifferentiableOn (by simp), hBi.mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 3) (𝓡 3) B p).IsInvertible := ⟨hB.mfderiv hp, rfl⟩
  obtain ⟨v, hv⟩ := hinv.surjective u
  have hlower (w : RoundCylinderCoordinates) :
      (r ^ 2 / 2) * ‖w‖ ^ 2 ≤ g.parametrizedCoefficients (centeredParametrization f q) (0, s) w w := by
    have h := normalizedCenteredCoefficients_lower g hε.le hεone hf.contMDiffOn hclose q hz w
    have hhalf : (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤
        normalizedCenteredCoefficients g f (r⁻¹ ^ 2) q (0, s) w w :=
      (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)).trans h
    change (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ r⁻¹ ^ 2 *
      g.parametrizedCoefficients (centeredParametrization f q) (0, s) w w at hhalf
    calc
      _ = r ^ 2 * ((1 / 2 : ℝ) * ‖w‖ ^ 2) := by ring
      _ ≤ r ^ 2 * (r⁻¹ ^ 2 * g.parametrizedCoefficients
          (centeredParametrization f q) (0, s) w w) :=
        mul_le_mul_of_nonneg_left hhalf (sq_nonneg r)
      _ = _ := by field_simp [hr.ne']
  have hell (w : EuclideanSpace ℝ (Fin 3)) :
      (A * r ^ 2) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients B p w w := by
    have h := quadratic_lower_rechart e
      (g.parametrizedCoefficients (centeredParametrization f q) (0, s)) hlower w
    rw [hchart]
    change _ ≤ g.parametrizedCoefficients (centeredParametrization f q ∘ e.symm) p w w
    erw [g.parametrizedCoefficients_comp_linear e.symm.toContinuousLinearMap
      ((centeredParametrization_contMDiffAt hf.contMDiffOn q (y := e.symm p)
        (by simpa only [p, e.symm_apply_apply] using hz)).mdifferentiableAt (by simp))]
    rw [show e.symm.toContinuousLinearMap p = (0, s) from e.symm_apply_apply _]
    exact h
  have hjet : ‖fderiv ℝ (g.pullbackCoefficients B) p‖ ≤ d * r ^ 2 * ε := by
    rw [hchart]
    have h := norm_fderiv_centeredParametrization_rechart_le g hε hεone hr
      hf.contMDiffOn hclose q hz e
    exact h.trans_eq (by dsimp only [d]; ring)
  have hunit : g.pullbackCoefficients B p v v = 1 := by
    have hpos : 0 ≤ g.inner (f (q, s)) u u := by
      by_cases hz : u = 0
      · simp [hz]
      · exact (g.pos (f (q, s)) u hz).le
    have hsq := congrArg (fun t : ℝ => t ^ 2) hu
    dsimp only [RiemannianMetric.tangentNorm] at hsq
    rw [Real.sq_sqrt hpos, one_pow] at hsq
    change g.inner (B p) (mfderiv (𝓡 3) (𝓡 3) B p v)
      (mfderiv (𝓡 3) (𝓡 3) B p v) = 1
    rw [hv, hpx]
    exact hsq
  have hcomp : (fun x : EuclideanSpace ℝ (Fin 3) => a (B x)) =ᶠ[𝓝 p] ell := by
    have hnear : ∀ᶠ y in 𝓝 p, (e.symm y).2 ∈ Ioo (-ε⁻¹) ε⁻¹ :=
      (continuous_snd.comp e.symm.continuous).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (by simpa only [Function.comp_apply, p, e.symm_apply_apply] using hz))
    filter_upwards [hnear] with y hy
    rw [hchart]
    exact havalue _ ⟨mem_univ _, hy⟩
  have haat : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ a (B p) := by
    rw [hpx]
    apply ha.contMDiffAt
    rw [← hf.isLocalHomeomorphOn.map_nhds_eq ⟨mem_univ q, hz⟩]
    exact Filter.image_mem_map ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ q, hz⟩)
  have h := CoordinateExponential.abs_linear_christoffel_le_of_scaled_controls
    ell hA hd hr hε.le hell hjet hunit
  have hess := EpsilonNeck.axial_hessian_of_smooth_parametrization D B hBs hBi hp haat hcomp v v
  rw [hv, hpx] at hess
  rw [hess, abs_neg]
  exact h

end PoincareConjecture.CylinderCover
