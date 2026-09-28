import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimumChartTests
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByPartsTests

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_chart_harmonic_of_modulus_minimum
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (b : M) {U : Set LoopPlane} (hU : IsOpen U)
    (hUinside : U ⊆ m64AnnulusInterior)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map U)
    (hfU : MapsTo A.map U (extChartAt (𝓡 n) b).source) :
    let u := (extChartAt (𝓡 n) b) ∘ A.map
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    ∀ z ∈ U,
      r • covDerivAlong (christoffelBilinear B) u (fun y => fderiv ℝ u y (e 0)) (e 0) z +
      r⁻¹ • covDerivAlong (christoffelBilinear B) u (fun y => fderiv ℝ u y (e 1)) (e 1) z =
        0 := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ A.map
  let B := g.pullbackCoefficients c.symm
  let Gamma := christoffelBilinear B
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let tau : LoopPlane → EuclideanSpace ℝ (Fin n) := fun x =>
    r • covDerivAlong Gamma u (fun y => fderiv ℝ u y (e 0)) (e 0) x +
    r⁻¹ • covDerivAlong Gamma u (fun y => fderiv ℝ u y (e 1)) (e 1) x
  have hu : ContDiffOn ℝ ∞ u U := by
    intro x hx
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (A.map x) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hfU hx)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hc.comp x (hf.contMDiffAt (hU.mem_nhds hx)))).contDiffWithinAt
  have htarget (x : LoopPlane) (hx : x ∈ U) : u x ∈ c.target := c.map_source (hfU hx)
  have hB (x : LoopPlane) (hx : x ∈ U) : ContDiffAt ℝ ∞ B (u x) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (htarget x hx))
  have hGamma (x : LoopPlane) (hx : x ∈ U) : ContDiffAt ℝ ∞ Gamma (u x) :=
    contDiffAt_christoffelBilinear (hB x hx)
      (g.isInvertible_chartCoefficients b (htarget x hx))
  have hcompat (x : LoopPlane) (hx : x ∈ U) : IsMetricCompatibleAt B Gamma (u x) :=
    isMetricCompatibleAt_chartCoefficients g b (htarget x hx)
  have htau : ContDiffOn ℝ ∞ tau U := by
    intro x hx
    have hup := hu.contDiffAt (hU.mem_nhds hx)
    have hi (i : Fin 2) : ContDiffAt ℝ ∞
        (fun z => covDerivAlong Gamma u (fun y => fderiv ℝ u y (e i)) (e i) z) x :=
      contDiffAt_covDerivAlong (hGamma x hx) hup
        ((hup.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const) (e i)
    exact (((contDiffAt_const (c := r)).smul (hi 0)).add
      ((contDiffAt_const (c := r⁻¹)).smul (hi 1))).contDiffWithinAt
  have hpair (w : EuclideanSpace ℝ (Fin n)) :
      EqOn (fun x => B (u x) w (tau x)) (fun _ => 0) U := by
    apply M60.eqOn_zero_of_integral_contDiff_smul_eq_zero
      (μ := (volume : Measure LoopPlane)) hU
    · intro x hx
      exact ((((hB x hx).comp x (hu.contDiffAt (hU.mem_nhds hx))).clm_apply
        contDiffAt_const).clm_apply
          (htau.contDiffAt (hU.mem_nhds hx))).continuousAt.continuousWithinAt
    · intro psi hpsi hpsic hpsiU
      let V : LoopPlane → EuclideanSpace ℝ (Fin n) := fun x => psi x • w
      have hV : ContDiff ℝ ∞ V := hpsi.smul contDiff_const
      have hVc : HasCompactSupport V := hpsic.smul_right
      have hVU : tsupport V ⊆ U :=
        (tsupport_smul_subset_left psi (fun _ => w)).trans hpsiU
      have hi (i : Fin 2) :=
        M60.covDerivAlong_trace_integration_by_parts (μ := volume) (fun _ : Fin 1 => e i)
          hU hu hV.contDiffOn hB hGamma hcompat hVc hVU
      simp only [Fin.sum_univ_one] at hi
      have ht := m64Annulus_chart_test_integral_eq_zero_of_modulus_minimum
        A hr hminimum hconformal b hU hUinside hf hfU V hV hVc hVU
      change (∫ x,
        r * B (u x) (covDerivAlong Gamma u V (e 0) x) (fderiv ℝ u x (e 0)) +
        r⁻¹ * B (u x) (covDerivAlong Gamma u V (e 1) x) (fderiv ℝ u x (e 1))) = 0 at ht
      rw [integral_add ((hi 0).1.const_mul r) ((hi 1).1.const_mul r⁻¹),
        integral_const_mul, integral_const_mul, (hi 0).2.2, (hi 1).2.2] at ht
      have hz : (∫ x, B (u x) (V x) (tau x)) = 0 := by
        simp only [tau, map_add, map_smul, smul_eq_mul]
        rw [integral_add ((hi 0).2.1.const_mul r) ((hi 1).2.1.const_mul r⁻¹),
          integral_const_mul, integral_const_mul]
        linarith
      simpa only [V, map_smul, smul_apply, smul_eq_mul] using hz
  change ∀ z ∈ U, tau z = 0
  intro z hz
  apply (g.isInvertible_chartCoefficients b (htarget z hz)).injective
  ext w
  simp only [map_zero, zero_apply]
  change B (u z) (tau z) w = 0
  have hsymm : B (u z) (tau z) w = B (u z) w (tau z) := g.symm _ _ _
  rw [hsymm]
  exact hpair w hz

end PoincareConjecture
