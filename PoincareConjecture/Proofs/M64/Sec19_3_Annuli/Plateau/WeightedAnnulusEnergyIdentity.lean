import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizer
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.WeightedAreaEnergy












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64ObservedWeakAnnulus_seed_weightedDensity_eq_ae
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1) (hmap : W.map = A.map)
    (hcol : ∀ i, ∀ᵐ p ∂mu, W.column i p =
      fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) (r : ℝ) :
    ∀ᵐ p ∂mu, (r * B (W.map p) (W.column 0 p) (W.column 0 p) +
      r⁻¹ * B (W.map p) (W.column 1 p) (W.column 1 p)) / 2 =
        (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  filter_upwards [hcol 0, hcol 1, ae_restrict_of_ae A.ae_manifold_differentiable,
    ae_restrict_mem isOpen_interior.measurableSet] with p h0 h1 hp hm
  rw [hmap, h0, h1,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he B hdiag (hp (interior_subset hm)) 0,
    m64ObservedMetric_diagonal_of_mDifferentiableAt g e he B hdiag (hp (interior_subset hm)) 1]



theorem m64ObservedWeakAnnulus_seed_weightedEnergy_eq
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1) (hmap : W.map = A.map)
    (hcol : ∀ i, ∀ᵐ p ∂mu, W.column i p =
      fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) (r : ℝ) :
    W.weightedEnergy B r = ∫ p in m64AnnulusDomain,
      (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  unfold M64ObservedWeakAnnulus.weightedEnergy
  rw [m64Annulus_restrict_closed_eq_interior]
  exact integral_congr_ae
    (m64ObservedWeakAnnulus_seed_weightedDensity_eq_ae A e he B hdiag W hmap hcol r)

variable [CompactSpace M] [T2Space M]



theorem M64Annulus.weightedGramEnergy_integrable
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) (r : ℝ) :
    IntegrableOn (fun p =>
      (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2)
        m64AnnulusDomain volume := by
  obtain ⟨d, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 d) 1 e := he.of_le (by simp)
  obtain ⟨B, K, hB, -, hb, -, -, hgram⟩ := m64ChartReadable_observed_metric g e he1 hread
  obtain ⟨W, hmap, hcol⟩ := m64ObservedWeakAnnulus_of_annulus A e he1
  have hdiag := m64ObservedMetric_tangent_diagonal g e he1 B hgram
  have hae := m64ObservedWeakAnnulus_seed_weightedDensity_eq_ae A e he1 B hdiag W hmap hcol r
  change Integrable _ (volume.restrict m64AnnulusDomain)
  rw [m64Annulus_restrict_closed_eq_interior]
  exact (W.weightedEnergy_integrable B hB hei.isEmbedding hb r).congr hae



theorem m64LeastAnnulusArea_le_seed_weightedEnergy
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    (W : M64ObservedWeakAnnulus (n := n) e c0 c1) (hmap : W.map = A.map)
    (hcol : ∀ i, ∀ᵐ p ∂mu, W.column i p =
      fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1)) {r : ℝ} (hr : 0 < r) :
    m64LeastAnnulusArea g c0 c1 ≤ W.weightedEnergy B r := by
  calc
    _ ≤ A.area := m64LeastAnnulusArea_le_annulus A
    _ ≤ ∫ p in m64AnnulusDomain,
        (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 :=
      A.area_le_weightedGramEnergy hr (A.weightedGramEnergy_integrable r)
    _ = _ := (m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he B hdiag W hmap hcol r).symm

omit [T2Space M] in


theorem m64ObservedWeakAnnulus_exists_seed_with_weightedEnergy
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1, W.map = A.map ∧
      ∀ r : ℝ, W.weightedEnergy B r = ∫ p in m64AnnulusDomain,
        (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2 := by
  obtain ⟨W, hmap, hcols⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  exact ⟨W, hmap, m64ObservedWeakAnnulus_seed_weightedEnergy_eq A e he B hdiag W hmap hcols⟩

end PoincareConjecture
