import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Contacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Normalization



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningStripExteriors

open PolygonalCrossingResolution NonspanningChainHole

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_annulus
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c : Bool → P2 → P2} {D T : Set P2} (E : NonspanningStripExteriors c D T)
    (hD : IsFinitePLBallPair P2 D (frontier D))
    (hdis : Disjoint (c false '' source) (c true '' source))
    {f : P2 → X} {τ : C3 → X} (hf : PolyhedralPLInCharts e f (T \ interior D))
    (hτ : PolyhedralPLInCharts e τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1)) :
    ∃ (N : NonspanningChainAnnulus E.hole) (g : P2 → X),
      PolyhedralPLInCharts e g Ann ∧
      (∀ i (x : E.hole.sourceSet i), g (N.copy i x) =
        pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i x) ∧
      g '' Ann = ⋃ i, pieceMap f (τ ∘ tubeArmOrientation E.s0 E.s1) i '' E.hole.sourceSet i := by
  have hLR : Disjoint (range E.leftArm) (range E.rightArm) := by
    change Disjoint (range (fun t : Icc (0 : ℝ) 1 ↦ c true ((t : ℝ), farArmParameter E.s1)))
      (range (fun t : Icc (0 : ℝ) 1 ↦ c false ((t : ℝ), farArmParameter E.s0)))
    rw [← arm_range, ← arm_range]
    exact hdis.symm.mono (image_mono (arm_far_subset_source E.s1))
      (image_mono (arm_far_subset_source E.s0))
  have hc := E.oriented_corner_equations h0 h1
  obtain ⟨u, hu, hkeep, himage⟩ := E.hole.exists_punctured_chain_map e hcompat
    E.retained_ball hD (E.retained_PL hD hf) (reoriented_tube_polyhedralPL e hτ E.s0 E.s1)
    hLR (fun t ↦ (hc t).1) (fun t ↦ (hc t).2.1)
      (fun t ↦ (hc t).2.2.1) (fun t ↦ (hc t).2.2.2)
  obtain ⟨N⟩ := E.hole.nonempty_normalization
  obtain ⟨g, hg, _, hcopy, himage'⟩ := N.exists_original_map e hu
  exact ⟨N, g, hg, fun i x ↦ (hcopy i x).trans (hkeep i x), himage'.trans himage⟩

end PoincareConjecture.M76.Dehn.NonspanningStripExteriors
