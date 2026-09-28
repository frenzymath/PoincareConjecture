import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalReflectedAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.ReflectionInsertion










set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



theorem OrdinaryDoubleCurveModel.exists_selfpaired_circle_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R)
    (hf : PolyhedralPLInCharts e f D2) (he : PLDomain e R)
    (hin : MapsTo f D2 R) (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : old.Index) (hself : old.mate i = i) (hiQ : Disjoint (old.pieces i) Q2) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  obtain ⟨D, hcore, _hcharts, _horder⟩ :=
    old.exists_selfpaired_circle_model hf he hin hfront i hself hiQ
  obtain ⟨A⟩ := D.nonempty_original_reflected_annulus hcore hf hin hfront hself
    (L := 1) (d := 1 / 8) (by norm_num) (by norm_num)
  exact old.exists_reflection_insertion hf he hin hfront A.depth_pos A.width_small
    (b := 1 / 16) (by norm_num) (by norm_num)
    A.tube A.tube_PL A.tube_fibers A.tube_interior A.source_interior
    A.chart A.chart_PL A.period_value A.full_preimage i A.double_trace A.middle

end PoincareConjecture.M76.Dehn
