import PoincareConjecture.Proofs.M63.Mathlib.AutonomousODERegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {gamma : ℝ → M} {S : Set ℝ}

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

theorem IsGeodesicOn.contMDiffOn_infty (hgamma : g.IsGeodesicOn gamma S) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma S :=
  fun _ ht => (hgamma.contMDiffAt_infty ht).contMDiffWithinAt

end PoincareConjecture.RiemannianMetric
