import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Ranks
import PoincareConjecture.Proofs.M76.Dehn.OriginalFaceMotionData
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

theorem FaceMotionData.finrank_plane
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} {j : V2 → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) :
    Module.finrank ℝ motion.plane.direction = if boundary = true then 2 else 3 := by
  exact MarkedSurfaceMotionData.finrank_plane motion

theorem FaceMotionData.original_intersection_rank_bounds
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} {j : V2 → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (A : SimplicialComplex ℝ V2) (hA : A.space = Metric.sphere (0 : V2) 1)
    {face old : Finset V2} (hface : face ∈ K.faces) (hold : old ∈ K.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old ∈ A.faces)
    {a b : Finset V3} (ha : a.card ≤ face.card) (hb : b.card ≤ old.card)
    (hrank : Module.finrank ℝ
      ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction) + Module.finrank ℝ motion.plane.direction =
          (a.card - 1) + (b.card - 1)) :
    let d := Module.finrank ℝ
      ((affineSpan ℝ (motion.coordinates.map 1 '' (a : Set V3)) ⊓
        affineSpan ℝ (b : Set V3)).direction)
    2 ≤ a.card ∧ 2 ≤ b.card ∧ d ≤ 1 ∧
      (boundary = true → d = 0) ∧
      ((face.card ≤ 2 ∨ old.card ≤ 2) → d = 0) ∧
      (boundary = false → 3 ≤ a.card ∨ 3 ≤ b.card) := by
  have hKdim (c : Finset V2) (hc : c ∈ K.faces) : c.card ≤ 3 := by
    have hbound := (K.indep hc).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] using hbound
  have hAdim (c : Finset V2) (hc : c ∈ A.faces) : c.card ≤ 2 := by
    have hint : interior A.space = ∅ := by rw [hA, interior_sphere']
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      A.face_card_le_of_interior_space_eq_empty hint hc
  exact MarkedSurfaceMotionData.surface_intersection_rank_bounds motion hKdim A hAdim
    hface hold hmarked ha hb hrank

end Geometry.OriginalPLTower
