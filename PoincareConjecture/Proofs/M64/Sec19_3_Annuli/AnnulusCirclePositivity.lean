import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CircleCurrentLaplacian
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCirclePeriodicity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.PeriodicHarmonicTransport














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory InnerProductSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64AnnulusCircleCurrent_harmonic_strip_of_conformal_minimum
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p) :
    HarmonicOnNhd (m64AnnulusCircleCurrent P t A.map 0) m64AnnulusOpenStrip := by
  apply m64PeriodicScalar_harmonicOnNhd_strip
    (fun p hp => m64AnnulusCircleCurrent_contDiffAt P t (hA p hp) 0)
    (m64AnnulusCircleCurrent_periodic P t A 0)
  apply m64AnnulusCircleCurrent_horizontal_harmonic_of_conformal_minimum
    P hcirc t A hminimum hconformal
  intro p hp
  have hsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    rw [← m64AnnulusInterior_closure]
    exact subset_closure
  exact (hA p (hsub hp)).contMDiffWithinAt






theorem m64AnnulusCircleCurrent_positive_of_boundary_nonneg
    (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    (hA : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t A.map 0 (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 ≤ m64AnnulusCircleCurrent P t A.map 0 (annulusPoint x 1))
    (hnonzero : ∃ p ∈ m64AnnulusDomain, m64AnnulusCircleCurrent P t A.map 0 p ≠ 0) :
    ∀ p ∈ m64AnnulusOpenStrip,
      0 < m64AnnulusCircleCurrent P t A.map 0 p := by
  exact m64PeriodicHarmonic_pos_of_boundary_nonneg
    (fun p hp =>
      (m64AnnulusCircleCurrent_contDiffAt P t (hA p hp) 0).continuousAt.continuousWithinAt)
    (m64AnnulusCircleCurrent_harmonic_strip_of_conformal_minimum P hcirc t A
      hminimum hconformal hA)
    (m64AnnulusCircleCurrent_periodic P t A 0) hlower hupper hnonzero

omit [T2Space M] [CompactSpace M] in




theorem m64Annulus_horizontal_column_ne_zero_of_circleCurrent_pos
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {p : LoopPlane}
    (hpos : 0 < m64AnnulusCircleCurrent P t f 0 p) :
    mfderiv (𝓡 2) (𝓡 (n + 1)) f p (EuclideanSpace.single (0 : Fin 2) 1) ≠ 0 := by
  intro hzero
  simp only [m64AnnulusCircleCurrent, hzero, map_zero, zero_apply] at hpos
  exact lt_irrefl (0 : ℝ) hpos

end PoincareConjecture
