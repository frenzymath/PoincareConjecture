import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusCollapse
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeTraceSubsequence














set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64




theorem free_labels_common_target_subsequence_of_discrepancy
    {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (e : X → E) (he : Continuous e) (hinj : Function.Injective e)
    (c0 c1 : ℝ → X) (hc0 : Continuous c0) (hc1 : Continuous c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (hzero : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e (c1 ((sigma1 j).map x)) - e (c0 ((sigma0 j).map x))‖ ^ 2) atTop (𝓝 0)) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ), StrictMono k ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c0 ((sigma0 (k j)).map x))
        atTop (𝓝 (c0 (L0 x)))) ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c1 ((sigma1 (k j)).map x))
        atTop (𝓝 (c1 (L1 x)))) ∧
      ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), c0 (L0 x) = c1 (L1 x) := by
  obtain ⟨k, L0, L1, hk, hm0, hm1, hP0, hP1, h00, h10, ht0, ht1⟩ :=
    degreeOneLift_pair_target_subsequence_ae c0 c1 hc0 hc1 hp0 hp1 sigma0 sigma1
  obtain ⟨R, hR⟩ := (isCompact_range he).isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg (e (c0 0))).trans (hR _ (mem_range_self (c0 0)))
  have hbound (x y : X) : ‖e y - e x‖ ^ 2 ≤ (2 * R) ^ 2 := by
    have hh : ‖e y - e x‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith [hR _ (mem_range_self x), hR _ (mem_range_self y)])
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  let D := fun x : ℝ => ‖e (c1 (L1 x)) - e (c0 (L0 x))‖ ^ 2
  have hDm : Measurable D := by
    have h1 : Measurable (fun x => e (c1 (L1 x))) :=
      (he.comp hc1).measurable.comp hm1.measurable
    have h0 : Measurable (fun x => e (c0 (L0 x))) :=
      (he.comp hc0).measurable.comp hm0.measurable
    exact (h1.sub h0).norm.pow_const 2
  have hDi : IntegrableOn D (Icc (0 : ℝ) curvePeriod) := by
    apply (show IntegrableOn (fun _ : ℝ => (2 * R) ^ 2) (Icc (0 : ℝ) curvePeriod) volume from
      integrableOn_const isCompact_Icc.measure_ne_top).mono' hDm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound _ _
  have hlim : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖e (c1 ((sigma1 (k j)).map x)) - e (c0 ((sigma0 (k j)).map x))‖ ^ 2)
      atTop (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod, D x)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * R) ^ 2)
    · intro j
      have h1 : Continuous (fun x => e (c1 ((sigma1 (k j)).map x))) :=
        (he.comp hc1).comp (degreeOneLift_continuous (sigma1 (k j)))
      have h0 : Continuous (fun x => e (c0 ((sigma0 (k j)).map x))) :=
        (he.comp hc0).comp (degreeOneLift_continuous (sigma0 (k j)))
      exact ((h1.sub h0).norm.pow 2).aestronglyMeasurable
    · exact integrableOn_const isCompact_Icc.measure_ne_top
    · intro j
      apply ae_of_all
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound _ _
    · filter_upwards [ae_restrict_of_ae ht0, ae_restrict_of_ae ht1] with x hx0 hx1
      exact (((he.tendsto _).comp hx1).sub ((he.tendsto _).comp hx0)).norm.pow 2
  have hDz : (∫ x in Icc (0 : ℝ) curvePeriod, D x) = 0 :=
    tendsto_nhds_unique hlim (hzero.comp hk.tendsto_atTop)
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun x => show 0 ≤ D x from sq_nonneg _)) hDi).mp hDz
  refine ⟨k, L0, L1, hk, hm0, hm1, hP0, hP1, h00, h10, ht0, ht1, ?_⟩
  filter_upwards [hae] with x hx
  have hnorm : ‖e (c1 (L1 x)) - e (c0 (L0 x))‖ = 0 := (sq_eq_zero_iff).mp hx
  exact (hinj (sub_eq_zero.mp (norm_eq_zero.mp hnorm))).symm

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem free_annulus_modulus_collapse_common_trace
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) (c0 c1 : ℝ → M)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (hs0 : ∀ j, ContDiff ℝ 1 (sigma0 j).map)
    (hs1 : ∀ j, ContDiff ℝ 1 (sigma1 j).map)
    (A : ∀ j, M64Annulus g (c0 ∘ (sigma0 j).map) (c1 ∘ (sigma1 j).map))
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hcollapse : Tendsto r atTop (𝓝 0))
    {K : ℝ} (henergy : ∀ j, m64ClassicalWeightedGramEnergy g (A j) (r j) ≤ K) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ), StrictMono k ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c0 ((sigma0 (k j)).map x))
        atTop (𝓝 (c0 (L0 x)))) ∧
      (∀ᵐ x ∂volume, Tendsto (fun j => c1 ((sigma1 (k j)).map x))
        atTop (𝓝 (c1 (L1 x)))) ∧
      ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) curvePeriod), c0 (L0 x) = c1 (L1 x) := by
  exact free_labels_common_target_subsequence_of_discrepancy e he.continuous hei.injective
    c0 c1 hc0.continuous hc1.continuous hp0 hp1 sigma0 sigma1
    (free_annulus_boundary_discrepancy_tendsto_zero_of_modulus_collapse
      g e he hei hread hc0 hc1 sigma0 sigma1 hs0 hs1 A r hr hcollapse henergy)

end PoincareConjecture.M64
