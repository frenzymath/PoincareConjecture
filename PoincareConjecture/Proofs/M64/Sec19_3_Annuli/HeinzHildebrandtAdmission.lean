import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyPipeline
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRegularity
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzArea

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

noncomputable def m64HeinzHildebrandtCertificate_of_global_C1
    (L : M64FiniteEnergyContinuousLimit (g := g))
    (hglobal : ContMDiffOn (𝓡 2) (𝓡 n) ∞ L.map (Set.univ : Set LoopPlane))
    (hperiodic : ∀ x s : ℝ,
      L.map (annulusPoint (x + curvePeriod) s) = L.map (annulusPoint x s))
    (hlower : ∀ x : ℝ, L.map (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, L.map (annulusPoint x 1) = c1 x)
    (hpiece : ∃ k : ℕ, 0 < k ∧ ∃ cut : Fin (k + 1) → ℝ,
      StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last k) = curvePeriod ∧
        ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 L.map
          {p : LoopPlane | cut j.castSucc ≤ p 0 ∧
            p 0 ≤ cut j.succ ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}) :
    M64HeinzHildebrandtBoundaryCertificate
      (g := g) (c0 := c0) (c1 := c1) L := by
  have hcontinuous : ContinuousOn L.map m64AnnulusDomain :=
    (hglobal.mono (subset_univ _)).continuousOn
  have hlocal : ∀ x ∈ m64AnnulusDomain, ∃ K : ℝ≥0, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ z ∈ U,
        g.edist (L.map y) (L.map z) ≤
          (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
    intro x hx
    exact m64_lipschitzOn_nhds_of_contMDiffAt g
      (((hglobal x (Set.mem_univ x)).of_le (by norm_num)).contMDiffAt
        (isOpen_univ.mem_nhds (Set.mem_univ x)))
  let hglobalLip := m64Annulus_hLip_of_local g hcontinuous hlocal
  let K : ℝ≥0 := Classical.choose hglobalLip
  have hK := Classical.choose_spec hglobalLip
  have hLip : ∀ x y : m64AnnulusDomain,
      g.edist (L.map x) (L.map y) ≤
        ENNReal.ofReal (K : ℝ) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    simpa [K, ENNReal.ofReal_eq_coe_nnreal] using hK x y
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  have hSsub : m64AnnulusInterior ⊆ m64AnnulusDomain := by
    intro p hp
    simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo] at hp
    change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    exact ⟨(hp 0 trivial).1.le, (hp 0 trivial).2.le,
      (hp 1 trivial).1.le, (hp 1 trivial).2.le⟩
  have hLipInterior : ∀ x ∈ m64AnnulusInterior, ∀ y ∈ m64AnnulusInterior,
      g.edist (L.map x) (L.map y) ≤
        ENNReal.ofReal (K : ℝ) * ENNReal.ofReal ‖x - y‖ := by
    intro x hx y hy
    exact hLip ⟨x, hSsub hx⟩ ⟨y, hSsub hy⟩
  have hdiffInterior := m60_ae_mdifferentiable_of_metric_lipschitzOn g
    isOpen_m64AnnulusInterior K.coe_nonneg hLipInterior
  have hdiff : ∀ᵐ p ∂volume,
      p ∈ m64AnnulusDomain →
        MDifferentiableAt (𝓡 2) (𝓡 n) L.map p := by
    filter_upwards [hdiffInterior, m64AnnulusDomain_ae_eq_interior] with p hp hpi
    intro hpdom
    exact hp (hpi.mp hpdom)
  have hintInterior := m60AreaIntegral_bound_of_metric_lipschitzOn g
    isOpen_m64AnnulusInterior hfinite K.coe_nonneg hLipInterior
  have hint : IntegrableOn (m60AreaDensity g L.map)
      m64AnnulusDomain volume := by
    exact (integrableOn_congr_set_ae m64AnnulusDomain_ae_eq_interior).mpr
      hintInterior.1
  exact {
    periodic := hperiodic
    lower_boundary := hlower
    upper_boundary := hupper
    lipschitz_constant := (K : ℝ)
    lipschitz_nonnegative := K.coe_nonneg
    lipschitz_on_domain := hLip
    ae_manifold_differentiable := hdiff
    area_integrable := hint
    piecewise_c1_on_limit := hpiece }

theorem m64Annulus_of_global_C1_limit
    (L : M64FiniteEnergyContinuousLimit (g := g))
    (hglobal : ContMDiffOn (𝓡 2) (𝓡 n) ∞ L.map (Set.univ : Set LoopPlane))
    (hperiodic : ∀ x s : ℝ,
      L.map (annulusPoint (x + curvePeriod) s) = L.map (annulusPoint x s))
    (hlower : ∀ x : ℝ, L.map (annulusPoint x 0) = c0 x)
    (hupper : ∀ x : ℝ, L.map (annulusPoint x 1) = c1 x)
    (hpiece : ∃ k : ℕ, 0 < k ∧ ∃ cut : Fin (k + 1) → ℝ,
      StrictMono cut ∧ cut 0 = 0 ∧ cut (Fin.last k) = curvePeriod ∧
        ∀ j : Fin k, ContMDiffOn (𝓡 2) (𝓡 n) 1 L.map
          {p : LoopPlane | cut j.castSucc ≤ p 0 ∧
            p 0 ≤ cut j.succ ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}) :
    ∃ A : M64Annulus g c0 c1,
      M64PiecewiseC1Annulus A ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map (interior m64AnnulusDomain) := by
  let H := m64HeinzHildebrandtCertificate_of_global_C1 L hglobal hperiodic
    hlower hupper hpiece
  let A := m64Annulus_of_heinzHildebrandt
    (c0 := c0) (c1 := c1) L H
  refine ⟨A, m64Annulus_of_heinzHildebrandt_piecewise_c1 L H, ?_⟩
  exact (hglobal.mono (by intro p hp; exact Set.mem_univ p))

end PoincareConjecture
