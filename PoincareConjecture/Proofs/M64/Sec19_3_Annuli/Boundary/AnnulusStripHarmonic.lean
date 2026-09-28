import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.PeriodicChartTension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

open CoordinateExponential

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem annulus_chart_harmonic_on_strip (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusOpenStrip) (b : M) :
    let q := extChartAt (𝓡 n) b
    let u := q ∘ A.map
    let B := g.pullbackCoefficients q.symm
    ∀ p ∈ m64AnnulusOpenStrip, A.map p ∈ q.source →
      annulusWeightedTension (christoffelBilinear B) u r p = 0 := by
  let q := extChartAt (𝓡 n) b
  let u := q ∘ A.map
  let B := g.pullbackCoefficients q.symm
  let Gamma := christoffelBilinear B
  let W := m64AnnulusOpenStrip ∩ A.map ⁻¹' q.source
  have hW : IsOpen W := hAi.continuousOn.isOpen_inter_preimage
    isOpen_m64AnnulusOpenStrip (isOpen_extChartAt_source b)
  have hu : ContDiffOn ℝ ∞ u W := by
    intro p hp
    have hq : ContMDiffAt (𝓡 n) (𝓡 n) ∞ q (A.map p) :=
      contMDiffAt_extChartAt' (by simpa only [mem_preimage, q, extChartAt_source] using hp.2)
    exact (contMDiffAt_iff_contDiffAt.mp (hq.comp p
      (hAi.contMDiffAt (isOpen_m64AnnulusOpenStrip.mem_nhds hp.1)))).contDiffWithinAt
  have hGamma (p : LoopPlane) (hp : p ∈ W) : ContDiffAt ℝ ∞ Gamma (u p) := by
    have ht : u p ∈ q.target := q.map_source hp.2
    exact contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients b).contDiffAt
        ((isOpen_extChartAt_target b).mem_nhds ht))
      (g.isInvertible_chartCoefficients b ht)
  have hperiod : ∀ x s, u (annulusPoint (x + curvePeriod) s) = u (annulusPoint x s) :=
    fun x s => congrArg q (A.periodic x s)
  apply annulus_periodic_zero_on_strip
    (annulusWeightedTension_periodic Gamma r hperiod) A.periodic hW
    (annulusWeightedTension_contDiffOn r hW hu hGamma).continuousOn
  intro p hp hs
  have hpi : p ∈ m64AnnulusOpenStrip := ((mem_m64AnnulusInterior_iff p).mp hp).2.2
  exact m64Annulus_chart_harmonic_of_modulus_minimum A hr hminimum hconformal b
    (hW.inter isOpen_m64AnnulusInterior) inter_subset_right
    (hAi.mono (fun _ hz => hz.1.1)) (fun _ hz => hz.1.2) p ⟨⟨hpi, hs⟩, hp⟩

end PoincareConjecture.M64
