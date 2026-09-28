import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusPeriodicHarmonicTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FreeRampBoundaryCurrent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusCircleCurrent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCirclePeriodicity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64FreeRampModulusMinimum_circleCurrent_pos
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (hr0 : M63IsRampAt P c0 t) (hr1 : M63IsRampAt P c1 t)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain,
      ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p) :
    ∀ p ∈ m64AnnulusOpenStrip,
      0 < m64AnnulusCircleCurrent P t A.map 0 p := by
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  have hAint : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map m64AnnulusInterior := by
    intro p hp
    exact (hA p (hsub hp)).contMDiffWithinAt
  let f : LoopPlane → ℝ := m64AnnulusCircleCurrent P t A.map 0
  have hreg : ∀ p ∈ m64AnnulusDomain, ContDiffAt ℝ ∞ f p := by
    intro p hp
    exact m64AnnulusCircleCurrent_contDiffAt P t (hA p hp) 0
  have hcont : ContinuousOn f m64AnnulusDomain := by
    intro p hp
    exact (hreg p hp).continuousAt.continuousWithinAt
  have hperiod : ∀ x s, f (annulusPoint (x + curvePeriod) s) =
      f (annulusPoint x s) := by
    intro x s
    exact m64AnnulusCircleCurrent_periodic P t A 0 x s
  have hf : ContDiffOn ℝ 2 f m64AnnulusOpenStrip := by
    intro p hp
    exact (m64PeriodicScalar_contDiffAt_of_fundamental hreg hperiod
      ⟨hp.1.le, hp.2.le⟩).of_le
      (by norm_cast : (2 : ℕ∞ω) ≤ ∞) |>.contDiffWithinAt
  have heq : ∀ p ∈ m64AnnulusInterior,
      r * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) p (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
    intro p hp
    simpa only [f] using
      m64AnnulusCircleCurrent_horizontal_equation_of_modulus_minimum P hcirc t A hr
        hminimum hconformal hAint hp
  have hstrip := m64PeriodicModulus_equation_on_strip hreg hperiod heq
  have hlower := m64AnnulusCircleCurrent_sign_of_free_ramp_boundary P t hp0 hc0 hr0 sigma0
    (fun x hx => hA _ ⟨hx.1, hx.2, le_rfl, zero_le_one⟩) A.lower_boundary
  have hupper := m64AnnulusCircleCurrent_sign_of_free_ramp_boundary P t hp1 hc1 hr1 sigma1
    (fun x hx => hA _ ⟨hx.1, hx.2, zero_le_one, le_rfl⟩) A.upper_boundary
  have hnonzero : ∃ p ∈ m64AnnulusDomain, f p ≠ 0 := by
    obtain ⟨x, hx, hpos⟩ := hlower.2
    exact ⟨annulusPoint x 0, ⟨hx.1.le, hx.2.le, le_rfl, zero_le_one⟩, hpos.ne'⟩
  exact m64PeriodicModulus_pos_of_boundary_nonneg hr hcont hf hstrip hperiod
    hlower.1 hupper.1 hnonzero

end PoincareConjecture
