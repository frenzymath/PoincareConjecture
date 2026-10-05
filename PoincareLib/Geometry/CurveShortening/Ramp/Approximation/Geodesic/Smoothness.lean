import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Autonomous.ODERegularity
import PoincareLib.Geometry.Riemannian.Coordinates.Continuation.Geodesic

/-!
# Smoothness of the actual M07 geodesics

The lower geodesic record gives actual coordinate derivative germs at every
included time. Smoothness of its actual metric geodesic field bootstraps
the same curve to all orders, including at endpoints. This supplies the
regularity needed for Definition 19.18 and Claims 19.19-19.20, MT2007 p. 450;
see `2026-09-21-geodesic-smoothness.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {gamma : ℝ → M} {S : Set ℝ}

/-- An actual intrinsic geodesic has smooth ambient germs at every included
time, even an endpoint. No completeness or positive speed is needed.
This is the regularity of the sides in MT2007 Definition 19.18, p. 450. -/
theorem IsGeodesicOn.contMDiffAt_infty (hgamma : g.IsGeodesicOn gamma S)
    {t : ℝ} (ht : t ∈ S) : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma t := by
  obtain ⟨p, q, w, h⟩ := hgamma t ht
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  have hqt := h.self_of_nhds.2.1
  have hB : ContDiffAt ℝ ∞ B (q t) :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqt)
  have hV := contDiffAt_coordinateGeodesicField hB
    (g.isInvertible_chartCoefficients p hqt) (z := (q t, w t))
  have hz : ContDiffAt ℝ ∞ (fun s => (q s, w s)) t :=
    contDiffAt_infty_of_hasDerivAt_comp hV
      (h.mono fun _ hs => hs.2.2.1.prodMk hs.2.2.2)
  have hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t :=
    contMDiffAt_iff_contDiffAt.mpr hz.fst
  have hinverse : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) p).symm (q t) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqt)
  exact (hinverse.comp t hq).congr_of_eventuallyEq (h.mono fun _ hs => hs.1)

/-- The existing M07 geodesic is smooth on its original parameter set.
The record's ambient germs make an openness premise unnecessary.
Definition 19.18 and Claims 19.19-19.20, MT2007 p. 450. -/
theorem IsGeodesicOn.contMDiffOn_infty (hgamma : g.IsGeodesicOn gamma S) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma S :=
  fun _ ht => (hgamma.contMDiffAt_infty ht).contMDiffWithinAt

end PoincareMT.RiemannianMetric
