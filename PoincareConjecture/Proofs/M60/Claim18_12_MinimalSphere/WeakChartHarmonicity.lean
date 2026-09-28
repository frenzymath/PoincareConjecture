import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.HarmonicSphereCharts
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByPartsTests










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60SphereChartHarmonic_of_test_integrals
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (htest : ∀ (b : M) (V : LoopPlane → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ∞ V → HasCompactSupport V →
      tsupport V ⊆ (f ∘ m60SphereParameter) ⁻¹' (extChartAt (𝓡 n) b).source →
      let u := (extChartAt (𝓡 n) b) ∘ (f ∘ m60SphereParameter)
      let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      ∫ z, ∑ i : Fin 2, B (u z)
        (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) z)
        (fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0) :
    M60SphereChartHarmonic g f := by
  intro b z hz
  let φ := f ∘ m60SphereParameter
  let c := extChartAt (𝓡 n) b
  let O := φ ⁻¹' c.source
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  let Γ := christoffelBilinear B
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let τ : LoopPlane → EuclideanSpace ℝ (Fin n) := fun x =>
    ∑ i : Fin 2, covDerivAlong Γ u (fun y => fderiv ℝ u y (e i)) (e i) x
  have hφ : ContMDiff (𝓡 2) (𝓡 n) ∞ φ := hf.comp m60SphereParameter_contMDiff
  have hO : IsOpen O := hφ.continuous.isOpen_preimage _ (isOpen_extChartAt_source b)
  have hu : ContDiffOn ℝ ∞ u O := by
    intro x hx
    have hx' : φ x ∈ (extChartAt (𝓡 n) b).source := hx
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ x) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx')
    exact (contMDiffAt_iff_contDiffAt.mp (hc.comp x hφ.contMDiffAt)).contDiffWithinAt
  have htarget (x : LoopPlane) (hx : x ∈ O) : u x ∈ c.target := c.map_source hx
  have hB (x : LoopPlane) (hx : x ∈ O) : ContDiffAt ℝ ∞ B (u x) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (htarget x hx))
  have hΓ (x : LoopPlane) (hx : x ∈ O) : ContDiffAt ℝ ∞ Γ (u x) :=
    contDiffAt_christoffelBilinear (hB x hx)
      (g.isInvertible_chartCoefficients b (htarget x hx))
  have hcompat (x : LoopPlane) (hx : x ∈ O) : IsMetricCompatibleAt B Γ (u x) :=
    isMetricCompatibleAt_chartCoefficients g b (htarget x hx)
  have hτ : ContDiffOn ℝ ∞ τ O := by
    apply ContDiffOn.sum
    intro i _ x hx
    have hup := hu.contDiffAt (hO.mem_nhds hx)
    exact (contDiffAt_covDerivAlong (hΓ x hx) hup
      ((hup.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const) (e i)).contDiffWithinAt
  have hpair (w : EuclideanSpace ℝ (Fin n)) :
      EqOn (fun x => B (u x) w (τ x)) (fun _ => 0) O := by
    apply M60.eqOn_zero_of_integral_contDiff_smul_eq_zero
      (μ := (volume : Measure LoopPlane)) hO
    · intro x hx
      exact ((((hB x hx).comp x (hu.contDiffAt (hO.mem_nhds hx))).clm_apply
        contDiffAt_const).clm_apply
          (hτ.contDiffAt (hO.mem_nhds hx))).continuousAt.continuousWithinAt
    · intro ψ hψ hψc hψO
      let V : LoopPlane → EuclideanSpace ℝ (Fin n) := fun x => ψ x • w
      have hV : ContDiff ℝ ∞ V := hψ.smul contDiff_const
      have hVc : HasCompactSupport V := hψc.smul_right
      have hVO : tsupport V ⊆ O := (tsupport_smul_subset_left ψ (fun _ => w)).trans hψO
      have hi := M60.covDerivAlong_trace_integration_by_parts (μ := volume) e
        hO hu hV.contDiffOn hB hΓ hcompat hVc hVO
      have ht := htest b V hV hVc hVO
      change (∫ x, ∑ i : Fin 2, B (u x) (covDerivAlong Γ u V (e i) x)
        (fderiv ℝ u x (e i))) = 0 at ht
      have hz' : (∫ x, B (u x) (V x) (τ x)) = 0 := by
        have hi' := hi.2.2
        change _ = -(∫ x, B (u x) (V x) (τ x)) at hi'
        linarith [hi']
      simpa only [V, map_smul, smul_apply, smul_eq_mul] using hz'
  have hzero : τ z = 0 := by
    apply (g.isInvertible_chartCoefficients b (htarget z hz)).injective
    ext w
    simp only [map_zero, zero_apply]
    change B (u z) (τ z) w = 0
    have hs : B (u z) (τ z) w = B (u z) w (τ z) := g.symm _ _ _
    rw [hs]
    exact hpair w hz
  simpa only [τ, Fin.sum_univ_two] using hzero

end PoincareConjecture
