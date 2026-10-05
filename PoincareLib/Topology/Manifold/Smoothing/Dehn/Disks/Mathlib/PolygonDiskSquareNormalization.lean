import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.SquarePolygonUniformBoundary
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallPairs

/-!
# Extend the prescribed whole square rim over the actual polygon disk

The actual disk pair and its prescribed boundary correspondence
give a total finite PL embedded square map. Its entire image is
the original disk, and its complete rim is exactly the polygon.
The fixed square loop retains the original uniform edge formulas.
See Dehn derivation 025, sections 3--5.
-/

set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- Extend the actual prescribed full rim over a produced polygon
disk. The output retains the entire image, embedding, exact rim
values and both directions of rim membership. This is a boundary
disk normalization, before the inward push. See Dehn025, section 5. -/
theorem exists_normalized_polygon_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {b : Set E}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ)) :
    ∃ (e : Q ≃ₜ P.boundary ℝ) (d : V2 → E), e.IsFinitePL ∧
      FinitePiecewiseAffineOn d D ∧ Topology.IsEmbedding (fun x : D => d x) ∧
      d '' D = b ∧ (∀ x : Q, d x = (e x : E)) ∧
      (∀ x : D, d x ∈ P.boundary ℝ ↔ (x : V2) ∈ Q) ∧
      (e squareRimBase : E) = P 0 ∧
      ∀ (i : Fin (n + 3)) (u s : unitInterval),
        (n + 3 : ℝ) * (s : ℝ) = (i : ℝ) + (u : ℝ) →
        (e (squareRimLoop s) : E) =
          AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) (u : ℝ) := by
  obtain ⟨e, he, hbase, hformula⟩ := exists_square_polygon_uniform_boundary P hP hinj
  obtain ⟨H, hH, hboundary, hiff⟩ :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_extension hb e he
  obtain ⟨d, hd, hHd⟩ := hH
  have hemb : Topology.IsEmbedding (fun x : D => d x) := by
    have hfun : (fun x : D => d x) = fun x : D => (H x : E) :=
      funext fun x => (hHd x).symm
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  have himage : d '' D = b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hHd ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hHd, H.apply_symm_apply]
  refine ⟨e, d, he, hd, hemb, himage, ?_, ?_, hbase, hformula⟩
  · intro x
    have h := congrArg Subtype.val (hboundary x)
    rw [hHd] at h
    exact h
  · intro x
    have h := hiff x
    rw [hHd] at h
    exact h.symm

end PoincareMT.M76.Dehn
