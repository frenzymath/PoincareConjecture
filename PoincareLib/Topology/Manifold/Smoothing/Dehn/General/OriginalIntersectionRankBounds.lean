import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Ranks
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceMotionData
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Simplicial.Mathlib.EmptyInteriorFaceDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Original square and whole-rim bounds for the actual intersections

The original source lies in dimension two, and its complete rim has
empty ambient interior. The actual motion plane has dimension three
in the interior phase and two in the boundary phase. Substitution in
the nonempty-intersection rank equation gives the required bounds.
See Hudson1969, Lemma4.6, and Dehn032, sections6--8.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- The actual produced affine comparison space has the original
ambient dimension, or the nonconstant boundary level's dimension.
No dimension hypothesis is supplied. See Dehn032, sections5--6. -/
theorem FaceMotionData.finrank_plane
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} {j : V2 → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) :
    Module.finrank ℝ motion.plane.direction = if boundary = true then 2 else 3 := by
  exact MarkedSurfaceMotionData.finrank_plane motion

/-- The retained exact rank equation and original source faces imply
rank at most one. Any original edge comparison has rank zero, every
boundary comparison has rank zero, and neither selected affine face
is a vertex. The interior phase cannot select two edges.
The complete rim supplies its own dimension bound.
See Dehn032, sections6--8. -/
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
