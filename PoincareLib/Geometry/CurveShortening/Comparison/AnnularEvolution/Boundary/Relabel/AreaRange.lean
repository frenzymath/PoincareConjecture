import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.FreeBoundaryTransport

/-!
# Exact annular area ranges under monotone boundary relabeling

The zero-area scalar collars transport every annulus in both directions
between the original and independently relabeled boundaries. Consequently
the full area ranges, their infima, and existence of minimizers agree.
The lifts may collapse intervals; no inverse lift is used.

This is boundary bookkeeping for Morgan--Tian Lemma 19.15, pp. 447-449,
and Lemma 19.31, pp. 464-466. See the auxiliary derivation at
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT.M64

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

/-- Reverse the first zero-area collar and retain the second one to relabel both boundaries
at exactly the original area. This supplies the fixed-to-free direction needed in MT2007
Lemma 19.31, pp. 464-466. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma
19.31, pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- Monotone Lipschitz degree-one boundary lifts preserve the entire set of admissible
annular areas, including when it is empty. The two actual collar constructions implement
MT2007 pp. 464-466. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma 19.31,
pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- The least annular area is unchanged by the boundary lifts because
the full area ranges coincide, not by unguarded infimum arithmetic.
Source: MT2007 Lemma 19.15, pp. 447-449. -/
theorem leastAnnulusArea_comp_lifts :
    m64LeastAnnulusArea g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) =
      m64LeastAnnulusArea g c0 c1 := by
  unfold m64LeastAnnulusArea
  rw [annulusAreaRange_comp_lifts hc0 hp0 hL0 hc1 hp1 hL1 sigma0 sigma1]

/-- Existence of an actual annulus is equivalent for the original and lifted boundaries.
This guards the geometric use of the infima in MT2007 Lemma 19.15, pp. 447-449. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma 19.31, pp. 464-466; project
derivation `proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- Existence of an attained admissible minimum is invariant under
monotone boundary lifts. The transported map is only asserted to be
Lipschitz; no smoothness or conformality is inferred from the collars.
Source: MT2007 Lemma 19.31, pp. 464-466. -/
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

/-- Periodic C1 curves supply their own global metric Lipschitz bounds, so area-range
invariance needs no separate distance estimate in the smooth-boundary application of MT2007
Lemma 19.31, pp. 464-466. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449, and Lemma
19.31, pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

/-- The periodic C1 version of the exact least-area identity used when free boundary labels
are selected in MT2007 pp. 447-449 and 464-466. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449, and Lemma 19.31, pp. 464-466; project derivation
`proof-work/tasks/M64/auxiliary/2026-09-25-boundary-relabel/DERIVATION.md`. -/
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

end PoincareMT.M64
