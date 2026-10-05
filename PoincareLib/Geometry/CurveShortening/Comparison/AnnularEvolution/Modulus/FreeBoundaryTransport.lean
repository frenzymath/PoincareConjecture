import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Free.BoundaryTransport
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Boundary.CurveLipschitz
import PoincareLib.Geometry.CurveShortening.Ramp.Slope.Slope.Regularity

/-!
# Actual free-boundary area transport for the supplied C2 curves

Periodic compactness of the actual speed proves global metric Lipschitz
control. The proved zero-area collars then restore literal boundary maps
at each included time. This is the free-label transport required by
MT2007 Lemma 19.15, pp. 447-449, after a moving variation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The lift's actual global Lipschitz bound supplies its continuity. Source: Morgan--Tian
(2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64PeriodicDegreeOneLift_continuous_map
    (sigma : M64PeriodicDegreeOneLift) : Continuous sigma.map := by
  have hLip : LipschitzWith
      (NNReal.mk sigma.lipschitz_constant sigma.lipschitz_nonnegative) sigma.map := by
    intro x y
    have hE := ENNReal.ofReal_le_ofReal (sigma.lipschitz_on x y)
    rw [ENNReal.ofReal_mul sigma.lipschitz_nonnegative] at hE
    simpa only [edist_dist, Real.dist_eq, ENNReal.coe_nnreal_eq, NNReal.coe_mk] using hE
  exact hLip.continuous

omit [T2Space M] in
/-- A periodic C1 curve has a global Lipschitz constant for the actual Riemannian distance,
obtained from its compact periodic speed range. Source: Morgan--Tian (2007), Lemma 19.15 and
Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64PeriodicC1Curve_metric_lipschitz (g : RiemannianMetric n M)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hperiod : Function.Periodic c curvePeriod) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ,
      g.edist (c x) (c y) ≤ ENNReal.ofReal L * ENNReal.ofReal |x - y| := by
  have hvel := m63CurveVelocity_periodic (hc.mdifferentiable one_ne_zero) hperiod
  have hspeed : Function.Periodic
      (fun x => g.tangentNorm (c x) (curveVelocity c x)) curvePeriod := by
    intro x
    change g.tangentNorm (c (x + curvePeriod)) (curveVelocity c (x + curvePeriod)) =
      g.tangentNorm (c x) (curveVelocity c x)
    have hv : curveVelocity c (x + curvePeriod) = curveVelocity c x := hvel x
    erw [hv, hperiod x]
  have hcont : Continuous (fun x => g.tangentNorm (c x) (curveVelocity c x)) :=
    M04.continuous_pathSpeed g hc
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  obtain ⟨B, hB⟩ := (hspeed.compact_of_continuous hP hcont).bddAbove
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  apply m60Curve_edist_le_of_speed_bound g hc (le_max_right _ _)
  intro x
  exact (hB (mem_range_self x)).trans (le_max_left _ _)

/-- At every included time, the actual C2 curves supply both zero-area collars, so every
free-boundary annulus has a literal-boundary annulus with exactly the same area. Source:
Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64C2ShrinkingCurves_freeBoundaryAreaTransport
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    M64FreeBoundaryAreaTransport (F.metric t) (fun x => c0 x t) (fun x => c1 x t) := by
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c0 x t) :=
    (hc0.spatial_regular t ht).of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c1 x t) :=
    (hc1.spatial_regular t ht).of_le (by norm_num)
  exact m64FreeBoundaryAreaTransport_of_collars h0.continuous (hc0.periodic t ht)
    (m64PeriodicC1Curve_metric_lipschitz (F.metric t) h0 (hc0.periodic t ht))
    h1.continuous (hc1.periodic t ht)
    (m64PeriodicC1Curve_metric_lipschitz (F.metric t) h1 (hc1.periodic t ht))

omit [T2Space M] in
/-- A free-boundary annulus attaining the original least area also minimizes among its own
literal lifted traces. Every competing lifted annulus is compared by the actual
area-preserving collars. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64FreeAnnulus_minimizes_own_boundary
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (htransport : M64FreeBoundaryAreaTransport g c0 c1)
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1) :
    A.area = m64LeastAnnulusArea g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) := by
  apply le_antisymm
  · apply le_csInf (m64AnnulusAreaRange_nonempty A)
    rintro _ ⟨B, rfl⟩
    obtain ⟨C, hC⟩ := htransport sigma0 sigma1 B
    calc
      A.area = m64LeastAnnulusArea g c0 c1 := hminimum
      _ ≤ C.area := m64LeastAnnulusArea_le_annulus C
      _ = B.area := hC
  · exact m64LeastAnnulusArea_le_annulus A

end PoincareMT
