import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyPipeline

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64_half_trace_le_sqrt_det_add
    {a b c epsilon scale : ℝ}
    (hepsilon : 0 ≤ epsilon) (hscale : 0 ≤ scale)
    (ha : |a - scale| ≤ epsilon)
    (hb : |b - scale| ≤ epsilon)
    (hc : |c| ≤ epsilon) :
    (a + b) / 2 ≤ Real.sqrt (max 0 (a * b - c * c)) + 3 * epsilon := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have htrace : (a + b) / 2 ≤ scale + epsilon := by
    linarith
  by_cases hsmall : scale < 2 * epsilon
  · have hsqrt : 0 ≤ Real.sqrt (max 0 (a * b - c * c)) :=
      Real.sqrt_nonneg _
    linarith
  · have htw : 2 * epsilon ≤ scale := le_of_not_gt hsmall
    have hsminus : 0 ≤ scale - epsilon := by linarith
    have hxa : 0 ≤ a - (scale - epsilon) := by linarith
    have hxb : 0 ≤ b - (scale - epsilon) := by linarith
    have hprod : (scale - epsilon) ^ 2 ≤ a * b := by
      have hxy : 0 ≤ (a - (scale - epsilon)) *
          (b - (scale - epsilon)) := mul_nonneg hxa hxb
      have hxs : 0 ≤ (a - (scale - epsilon)) * (scale - epsilon) :=
        mul_nonneg hxa hsminus
      have hys : 0 ≤ (b - (scale - epsilon)) * (scale - epsilon) :=
        mul_nonneg hxb hsminus
      nlinarith
    have hplus : 0 ≤ epsilon + c := by linarith
    have hminus : 0 ≤ epsilon - c := by linarith
    have hcross : c ^ 2 ≤ epsilon ^ 2 := by
      have hprod' : 0 ≤ (epsilon - c) * (epsilon + c) :=
        mul_nonneg hminus hplus
      nlinarith
    have hdet : (scale - 2 * epsilon) ^ 2 ≤ a * b - c * c := by
      nlinarith [hprod, hcross]
    have hdet' : (scale - 2 * epsilon) ^ 2 ≤
        max 0 (a * b - c * c) := hdet.trans (le_max_right _ _)
    have hsqrt : scale - 2 * epsilon ≤
        Real.sqrt (max 0 (a * b - c * c)) :=
      Real.le_sqrt_of_sq_le hdet'
    linarith

theorem m64EnergyDensity_le_areaDensity_add_of_gram_defect
    (g : RiemannianMetric n M) (f : LoopPlane → M) (p : LoopPlane)
    {epsilon scale : ℝ} (hepsilon : 0 ≤ epsilon) (hscale : 0 ≤ scale)
    (h00 : |m60AreaGram g f p 0 0 - scale| ≤ epsilon)
    (h11 : |m60AreaGram g f p 1 1 - scale| ≤ epsilon)
    (h01 : |m60AreaGram g f p 0 1| ≤ epsilon) :
    m60EnergyDensity g f p ≤ m60AreaDensity g f p + 3 * epsilon := by
  have h := m64_half_trace_le_sqrt_det_add
    (a := m60AreaGram g f p 0 0)
    (b := m60AreaGram g f p 1 1)
    (c := m60AreaGram g f p 0 1)
    hepsilon hscale h00 h11 h01
  simp only [m60EnergyDensity, m60AreaDensity, Matrix.trace_fin_two,
    Matrix.det_fin_two, m60AreaGram_symm g f p 1 0, div_eq_mul_inv]
  nlinarith [h]

theorem M64Annulus.energy_le_area_add_of_nearlyConformal
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {epsilon : ℝ}
    (hconf : M64AnnulusGramNearlyConformal (g := g) A.map epsilon)
    (hmeas : MeasurableSet m64AnnulusDomain)
    (hE : IntegrableOn (m60EnergyDensity g A.map)
      m64AnnulusDomain volume)
    (hnull : volume (m64AnnulusDomain \ interior m64AnnulusDomain) = 0) :
    (∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p) ≤
      A.area + 3 * epsilon * volume.real m64AnnulusDomain := by
  have hconst : IntegrableOn (fun _ : LoopPlane => 3 * epsilon)
      m64AnnulusDomain volume := integrableOn_const
        m64AnnulusDomain_volume_ne_top
  have hboundary : ∀ᵐ p ∂volume,
      p ∉ (m64AnnulusDomain \ interior m64AnnulusDomain) :=
    by
      rw [ae_iff]
      have hset : {a : LoopPlane |
          ¬a ∉ m64AnnulusDomain \ interior m64AnnulusDomain} =
          m64AnnulusDomain \ interior m64AnnulusDomain := by
        ext a
        simp
      rw [hset]
      exact hnull
  have hbound : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60EnergyDensity g A.map p ≤
        m60AreaDensity g A.map p + 3 * epsilon := by
    filter_upwards [ae_restrict_of_ae hboundary,
      ae_restrict_of_ae hconf.2, ae_restrict_mem hmeas] with p hpb hpc hpd
    have hpint : p ∈ interior m64AnnulusDomain := by
      by_contra hpint
      exact hpb ⟨hpd, hpint⟩
    obtain ⟨scale, hscale, hgram⟩ := hpc hpint
    have h00 := hgram 0 0
    have h11 := hgram 1 1
    have h01 := hgram 0 1
    have h00' : |m60AreaGram g A.map p 0 0 - scale| ≤ epsilon := by
      simpa [m60AreaGram] using h00
    have h11' : |m60AreaGram g A.map p 1 1 - scale| ≤ epsilon := by
      simpa [m60AreaGram] using h11
    have h01' : |m60AreaGram g A.map p 0 1| ≤ epsilon := by
      simpa [m60AreaGram] using h01
    exact m64EnergyDensity_le_areaDensity_add_of_gram_defect g A.map p
      hconf.1 hscale h00' h11' h01'
  have hright : IntegrableOn
      (fun p => m60AreaDensity g A.map p + 3 * epsilon)
      m64AnnulusDomain volume := A.area_integrable.add hconst
  calc
    (∫ p in m64AnnulusDomain, m60EnergyDensity g A.map p) ≤
        ∫ p in m64AnnulusDomain,
          (m60AreaDensity g A.map p + 3 * epsilon) :=
      integral_mono_ae hE hright hbound
    _ = A.area + 3 * epsilon * volume.real m64AnnulusDomain := by
      rw [integral_add A.area_integrable hconst]
      simp [M64Annulus.area, m64AnnulusArea, mul_comm]

end PoincareConjecture
