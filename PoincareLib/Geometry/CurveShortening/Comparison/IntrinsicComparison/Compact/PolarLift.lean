import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Compact.RadialConfinement
import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Compact.UniqueLift
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Continuous.PolarLift
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Continued.Polar

/-!
# Continuous boundary lifts from unique confined radial vectors

Compactness of the closed confined vector class makes its unique endpoint
selection continuous. This proves the continuity assertion in
Morgan--Tian, Remark 19.42, p. 472, once geometric existence and uniqueness
have been supplied. It does not infer radial uniqueness from minimization.
-/

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareMT

/-- Unique bounded confined radial vectors over a boundary arc give an
actual continuous closed-interval lift. The hypotheses quantify over all
such vectors, not only minimizing geodesics. Source: Morgan--Tian,
Remark 19.42, p. 472; see the compact-fiber derivation. -/
theorem m64Intrinsic_exists_continuous_confined_boundary_lift
    {e : AnnulusCoordinates → AnnulusCoordinates} {R a b radius : ℝ}
    (he : ContinuousOn e (closedBall 0 R))
    {B : Set AnnulusCoordinates} (hB : IsClosed B)
    (hunique : ∀ s ∈ Icc a b, ∃! v : AnnulusCoordinates,
      (‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ B) ∧
        e v = intrinsicAnnulusBoundary radius s) :
    ∃ u : ℝ → AnnulusCoordinates, ContinuousOn u (Icc a b) ∧
      (∀ s ∈ Icc a b, ‖u s‖ ≤ R) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, e (t • u s) ∈ B) ∧
      ∀ s ∈ Icc a b, e (u s) = intrinsicAnnulusBoundary radius s := by
  classical
  let C : Set AnnulusCoordinates :=
    {v | ‖v‖ ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) ∈ B}
  have hC : IsCompact C := m64_isCompact_confined_radial_vectors he hB
  have heC : ContinuousOn e C := he.mono (by
    intro v hv
    simpa only [mem_closedBall, dist_zero_right] using hv.1)
  obtain ⟨v, hv, hvC⟩ := m64_exists_continuous_lift_of_compact_unique_fibers
    hC heC isCompact_Icc (m64Intrinsic_contDiff_boundary radius).continuous.continuousOn
    hunique
  let u : ℝ → AnnulusCoordinates := fun s => if hs : s ∈ Icc a b then v ⟨s, hs⟩ else 0
  have hu (s : ℝ) (hs : s ∈ Icc a b) : u s = v ⟨s, hs⟩ := dif_pos hs
  have huc : ContinuousOn u (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hv.congr (fun s => (hu s s.property).symm)
  refine ⟨u, huc, ?_, ?_, ?_⟩
  · intro s hs
    rw [hu s hs]
    exact (hvC ⟨s, hs⟩).1.1
  · intro s hs t ht
    rw [hu s hs]
    exact (hvC ⟨s, hs⟩).1.2 t ht
  · intro s hs
    rw [hu s hs]
    exact (hvC ⟨s, hs⟩).2

end PoincareMT
