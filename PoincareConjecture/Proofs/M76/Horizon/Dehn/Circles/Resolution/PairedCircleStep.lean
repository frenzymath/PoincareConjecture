import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.NestedCircleStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.DisjointCircleStep
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.PairedMarkedModel










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem OrdinaryDoubleCurveModel.exists_paired_circle_resolution
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (old : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (he : PLDomain e R) (hin : MapsTo f D2 R)
    (hfront : ∀ x ∈ D2, f x ∈ frontier R ↔ x ∈ Q2)
    (i : old.Index) (hi : old.mate i ≠ i)
    {n : ℕ} (P : Polygon V2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPs : P.boundary ℝ = old.pieces i)
    (hQ : Disjoint (old.pieces i) Q2) :
    ∃ g : V2 → X, PolyhedralPLInCharts e g D2 ∧ MapsTo g D2 R ∧ EqOn g f Q2 ∧
      (∀ x ∈ D2, g x ∈ frontier R ↔ x ∈ Q2) ∧
      doubleBoundaryComponentCount g D2 Q2 ≤ doubleBoundaryComponentCount f D2 Q2 ∧
      doubleInteriorComponentCount g D2 Q2 < doubleInteriorComponentCount f D2 Q2 ∧
      Nonempty (OrdinaryDoubleCurveModel e g R) := by
  obtain ⟨D, _, _, _, hcore, _⟩ := old.exists_paired_circle_marked_model
    hf he hin hfront i hi P hP hPi hPs hQ
  obtain ⟨G⟩ := D.nonempty_paired_circle_collars hcore hfront P hP hPi hPs
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  rcases G.source_cases with hn | hn | hdis
  · exact G.exists_nested_circle_resolution (by norm_num) (by norm_num)
      (b := 1 / 2) (by norm_num) (by norm_num) hf he.compatible hin hfront 0 hn
  · exact G.exists_nested_circle_resolution (by norm_num) (by norm_num)
      (b := 1 / 2) (by norm_num) (by norm_num) hf he.compatible hin hfront 1 hn
  · exact G.exists_disjoint_circle_resolution (by norm_num) (by norm_num)
      (b := 1 / 2) (by norm_num) (by norm_num) hf he.compatible hin hfront hdis

end PoincareConjecture.M76.Dehn
