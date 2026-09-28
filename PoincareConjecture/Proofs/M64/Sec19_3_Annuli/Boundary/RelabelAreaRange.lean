import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport














set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

section Lipschitz

variable (hc0 : Continuous c0) (hp0 : Function.Periodic c0 curvePeriod)
  (hL0 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ,
    g.edist (c0 x) (c0 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)
  (hc1 : Continuous c1) (hp1 : Function.Periodic c1 curvePeriod)
  (hL1 : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ,
    g.edist (c1 x) (c1 y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y|)
  (sigma0 sigma1 : M64PeriodicDegreeOneLift)

include hc0 hp0 hL0 hc1 hp1 hL1






theorem annulus_exists_relabel_boundaries (A : M64Annulus g c0 c1) :
    ∃ B : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map), B.area = A.area := by
  obtain ⟨C0, _hmap0, harea0⟩ := m64_zero_area_boundary_collar g c0 sigma0.map
    hc0 hp0 hL0 (m64PeriodicDegreeOneLift_continuous_map sigma0) sigma0.period_shift
    ⟨sigma0.lipschitz_constant, sigma0.lipschitz_nonnegative, sigma0.lipschitz_on⟩
  obtain ⟨C1, _hmap1, harea1⟩ := m64_zero_area_boundary_collar g c1 sigma1.map
    hc1 hp1 hL1 (m64PeriodicDegreeOneLift_continuous_map sigma1) sigma1.period_shift
    ⟨sigma1.lipschitz_constant, sigma1.lipschitz_nonnegative, sigma1.lipschitz_on⟩
  obtain ⟨D, _hmapD, hareaD⟩ := m64Annulus_join_with_area (m64Annulus_reverse C0) A
  obtain ⟨B, _hmapB, hareaB⟩ := m64Annulus_join_with_area D C1
  refine ⟨B, ?_⟩
  rw [hareaB, hareaD, m64Annulus_reverse_area, harea0, harea1, zero_add, add_zero]






theorem annulusAreaRange_comp_lifts :
    m64AnnulusAreaRange g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) =
      m64AnnulusAreaRange g c0 c1 := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩
    obtain ⟨B, hB⟩ := m64FreeBoundaryAreaTransport_of_collars
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B, hB⟩
  · rintro ⟨A, rfl⟩
    obtain ⟨B, hB⟩ := annulus_exists_relabel_boundaries
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B, hB⟩




theorem leastAnnulusArea_comp_lifts :
    m64LeastAnnulusArea g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) =
      m64LeastAnnulusArea g c0 c1 := by
  unfold m64LeastAnnulusArea
  rw [annulusAreaRange_comp_lifts hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1]





theorem nonempty_annulus_comp_lifts_iff :
    Nonempty (M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)) ↔
      Nonempty (M64Annulus g c0 c1) := by
  constructor
  · rintro ⟨A⟩
    obtain ⟨B, _hB⟩ := m64FreeBoundaryAreaTransport_of_collars
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B⟩
  · rintro ⟨A⟩
    obtain ⟨B, _hB⟩ := annulus_exists_relabel_boundaries
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B⟩





theorem exists_minimum_comp_lifts_iff :
    (∃ A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
      A.area = m64LeastAnnulusArea g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)) ↔
    (∃ A : M64Annulus g c0 c1, A.area = m64LeastAnnulusArea g c0 c1) := by
  have hinf := leastAnnulusArea_comp_lifts hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨B, hB⟩ := m64FreeBoundaryAreaTransport_of_collars
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B, hB.trans (hA.trans hinf)⟩
  · rintro ⟨A, hA⟩
    obtain ⟨B, hB⟩ := annulus_exists_relabel_boundaries
      hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1 A
    exact ⟨B, hB.trans (hA.trans hinf.symm)⟩

end Lipschitz






theorem annulusAreaRange_comp_lifts_of_C1
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hp0 : Function.Periodic c0 curvePeriod)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift) :
    m64AnnulusAreaRange g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) =
      m64AnnulusAreaRange g c0 c1 :=
  annulusAreaRange_comp_lifts hc0.continuous hp0
    (m64PeriodicC1Curve_metric_lipschitz g hc0 hp0) hc1.continuous hp1
    (m64PeriodicC1Curve_metric_lipschitz g hc1 hp1) sigma0 sigma1





theorem leastAnnulusArea_comp_lifts_of_C1
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hp0 : Function.Periodic c0 curvePeriod)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1)
    (hp1 : Function.Periodic c1 curvePeriod)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift) :
    m64LeastAnnulusArea g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) =
      m64LeastAnnulusArea g c0 c1 := by
  unfold m64LeastAnnulusArea
  rw [annulusAreaRange_comp_lifts_of_C1 hc0 hp0 hc1 hp1 sigma0 sigma1]

end PoincareConjecture.M64
