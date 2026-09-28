import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeProductVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeAnnulusFamily
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ForwardMinimalCompetitor














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}







theorem m64FreeCircleProductAnnulus_modulus_exists_forward
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  obtain ⟨delta, hdelta, U, hU, hDU, v, hv, hbase, hperiodic, _hlo, _hup,
      hvelocity0, hvelocity1, hadmit⟩ :=
    m64FreeAnnulus_exists_c2_moving_family_with_literal_competitors
      P.flow hc0 hc1 ht sigma0 sigma1 A hO hdom hA
  have hforward := (m64FreeCircleProductAnnulus_modulus_sharp_variation
    P hn hcirc hc0 hc1 ht sigma0 sigma1 A hr hminimum hconformal hO hdom hA
    hK hcurv hdelta hU hDU hv hbase hperiodic hvelocity0 hvelocity1).2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-delta) delta :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, hdelta⟩)
  intro eta heta
  filter_upwards [hforward eta heta, hsmall] with h hh hδ
  obtain ⟨B, hB⟩ := hadmit h hδ
  exact ⟨B, hB.trans_le hh⟩





theorem m64FreeCircleProductAnnulus_modulus_exists_forward_with_curvature_supremum
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∃ B : M64Annulus (P.flow.metric (t + h))
          (fun x => c0 x (t + h)) (fun x => c1 x (t + h)),
        B.area ≤ A.area +
          h * ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * A.area + eta) := by
  have hbounded := m64CurvatureRange_bddAbove_of_compact
    (F := F) isCompact_univ (Ioo_subset_Icc_self ht)
  exact m64FreeCircleProductAnnulus_modulus_exists_forward P hn hcirc hc0 hc1 ht
    sigma0 sigma1 A hr hminimum hconformal hO hdom hA
    (m64CurvatureSupremum_nonneg hbounded) (m64Curvature_le_supremum hbounded)






theorem m64AnnulusFlow_forward_of_free_modulus_minimum
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {c0 c1 : ℝ → ℝ → P.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn P.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn P.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (P.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O) :
    AnnulusForwardDerivativeBound (m64FlowAnnulusArea P c0 c1)
      ((2 * (n : ℝ) - 1) * m64CurvatureSupremum F t * m64FlowAnnulusArea P c0 c1 t) t := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  obtain ⟨A0, hA0⟩ := m64C2ShrinkingCurves_freeBoundaryAreaTransport P.flow hc0 hc1
    (Ioo_subset_Icc_self ht) sigma0 sigma1 A
  have hcomp := m64FreeCircleProductAnnulus_modulus_exists_forward_with_curvature_supremum
    P hn hcirc hc0 hc1 ht sigma0 sigma1 A hr hminimum hconformal hO hdom hA
  apply m64AnnulusForward_of_minimal_competitors A0 (hA0.trans hminimum)
  intro eta heta
  filter_upwards [hcomp eta heta] with h hh
  obtain ⟨B, hB⟩ := hh
  refine ⟨B, ?_⟩
  rw [hminimum] at hB
  rw [hA0, hminimum]
  exact hB

end PoincareConjecture
