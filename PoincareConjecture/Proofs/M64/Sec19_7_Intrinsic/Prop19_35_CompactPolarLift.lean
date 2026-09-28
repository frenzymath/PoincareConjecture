import PoincareConjecture.Proofs.M64.Mathlib.CompactRadialConfinement
import PoincareConjecture.Proofs.M64.Mathlib.CompactUniqueLift
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuousPolarLift
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuedPolar

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

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

end PoincareConjecture
