import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedCircleStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OrdinaryCounts









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_disk_without_paired_interior_circles
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2) :
    ∃ (g : V2 → X) (model : OrdinaryDoubleCurveModel e g R),
      PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 ≤ doubleInteriorComponentCount f D2 Q2 ∧
      ∀ i, Disjoint (model.pieces i) Q2 → model.mate i = i := by
  classical
  generalize hn : doubleInteriorComponentCount f D2 Q2 = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hself : ∀ i, Disjoint (old.pieces i) Q2 → old.mate i = i
    · exact ⟨f, old, hf, hin, fun _ _ => rfl, hfront, le_rfl, hn.le, hself⟩
    push Not at hself
    obtain ⟨i, hQ, hi⟩ := hself
    have hpoly : ∃ (m : ℕ) (P : Polygon V2 (m + 3)), Function.Injective P ∧
        P.HasSimplicialEdges ∧ P.boundary ℝ = old.pieces i := by
      rcases old.models i with hb | ⟨m, P, hPi, hP, hPs, _⟩
      · obtain ⟨x, hx, hxQ⟩ := (old.interval_iff_meets_rim i).mp hb
        exact (disjoint_left.mp hQ hx hxQ).elim
      · exact ⟨m, P, hPi, hP, hPs⟩
    obtain ⟨m, P, hPi, hP, hPs⟩ := hpoly
    obtain ⟨g, hg, hgR, hgr, hgfront, hboundary, hless, ⟨model⟩⟩ :=
      old.exists_paired_circle_resolution hf he hin hfront i hi P hP hPi hPs hQ
    obtain ⟨g', model', hg', hg'R, hg'r, hg'front, hboundary', hcircle', hself'⟩ :=
      ih (doubleInteriorComponentCount g D2 Q2) (hn ▸ hless) model hg hgR hgfront rfl
    exact ⟨g', model', hg', hg'R, hg'r.trans hgr, hg'front,
      hboundary'.trans hboundary, hcircle'.trans (hn ▸ hless.le), hself'⟩

end PoincareConjecture.M76.Dehn
