import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.SelfPairedCircleStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedCircleStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OrdinaryCounts

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_disk_without_interior_double_curves
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    ∃ (g : V2 → X) (_model : OrdinaryDoubleCurveModel e g R),
      PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 = 0 := by
  classical
  generalize hn : doubleInteriorComponentCount f D2 Q2 = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hzero : doubleInteriorComponentCount f D2 Q2 = 0
    · exact ⟨f, old, hf, hin, fun _ _ ↦ rfl, hfront, le_rfl, hzero⟩
    obtain ⟨i, m, P, hPi, hP, hPs, hiQ⟩ :=
      old.exists_polygon_of_interior_count_pos (Nat.pos_of_ne_zero hzero)
    have hstep : ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧
        MapsTo g D2 R ∧ EqOn g f Q2 ∧
        (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
        doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
        doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
        Nonempty (OrdinaryDoubleCurveModel e g R) := by
      by_cases hself : old.mate i = i
      · exact old.exists_selfpaired_circle_resolution hf he hin hfront i hself hiQ
      · exact old.exists_paired_circle_resolution hf he hin hfront i hself P hP hPi hPs hiQ
    obtain ⟨g, hg, hgR, hgRim, hgFront, hgBoundary, hgLess, ⟨model⟩⟩ := hstep
    obtain ⟨g', model', hg', hg'R, hg'Rim, hg'Front, hg'Boundary, hg'Zero⟩ :=
      ih (doubleInteriorComponentCount g D2 Q2) (hn ▸ hgLess) model hg hgR hgFront rfl
    exact ⟨g', model', hg', hg'R, hg'Rim.trans hgRim, hg'Front,
      hg'Boundary.trans hgBoundary, hg'Zero⟩

end PoincareConjecture.M76.Dehn
