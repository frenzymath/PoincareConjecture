import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningPathPolygon
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ)



theorem exists_finite_pl_returning_bigon {W : Set V} {a b : V}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hup : ∀ x ∈ W, 0 ≤ x.2) (haxis : W ∩ Z = {a, b}) :
    ∃ (n : ℕ) (P : Polygon V (n + 3)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      (∀ i, 0 ≤ (P i).2) ∧ P.boundary ℝ = W ∪ segment ℝ a b ∧
      IsFinitePLBallPair V (closure P.inside) (W ∪ segment ℝ a b) ∧
      IsCompact (closure P.inside) ∧
      closure P.inside ∩ Z = segment ℝ a b ∧
      ∀ C : Set V, Convex ℝ C → W ⊆ C → closure P.inside ⊆ C := by
  obtain ⟨n, p, hp, hp0, hp1, hpW, hinter, _⟩ :=
    hW.exists_simplicial_path_with_endpoints hab
  obtain ⟨P, hP, hi, hPu, hboundary⟩ :=
    Polygon.exists_polygon_of_returning_path (n := n + 2) p hp hinter
      (by simpa only [hpW, hp0, hp1] using haxis)
      (fun i => hup _ (hpW ▸ Polygon.vertex_mem_pathCarrier p i))
  have hbd : P.boundary ℝ = W ∪ segment ℝ a b := by
    simpa only [hpW, hp0, hp1] using hboundary
  refine ⟨n + 2, P, hP, hi, hPu, hbd, ?_, P.isCompact_closure_inside hP hi,
    P.returning_closed_inside_axis hP hi hPu hbd haxis, ?_⟩
  · rw [← hbd]
    exact P.isFinitePLBallPair_closed_inside hP hi
  · intro C hC hWC
    apply P.closure_inside_subset_convex hP hi hC
    rintro _ ⟨i, rfl⟩
    rcases hbd ▸ P.vertex_mem_boundary i with hx | hx
    · exact hWC hx
    · exact hC.segment_subset (hWC (hW.1 (by simp))) (hWC (hW.1 (by simp))) hx

end PoincareConjecture.M76
