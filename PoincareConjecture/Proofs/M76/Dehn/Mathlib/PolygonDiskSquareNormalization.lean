import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquarePolygonUniformBoundary
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs

set_option autoImplicit false

open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

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

end PoincareConjecture.M76.Dehn
