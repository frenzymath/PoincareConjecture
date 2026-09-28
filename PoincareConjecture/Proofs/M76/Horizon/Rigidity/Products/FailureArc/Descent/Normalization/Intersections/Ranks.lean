import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension
import Mathlib.LinearAlgebra.Dual.Lemmas










set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}




theorem MarkedSurfaceMotionData.finrank_plane
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary) :
    Module.finrank ℝ motion.plane.direction = if boundary = true then 2 else 3 := by
  cases boundary with
  | false =>
    change Module.finrank ℝ motion.plane.direction = 3
    rw [motion.interior_plane rfl]
    rw [AffineSubspace.direction_top, finrank_top]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  | true =>
    obtain ⟨ell, hell, _, hdir, _⟩ := motion.boundary_plane rfl
    have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
    change Module.finrank ℝ motion.plane.direction = 2
    rw [hdir]
    omega







theorem MarkedSurfaceMotionData.surface_intersection_rank_bounds
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    {Q : OpenPartialHomeomorph t.Carrier V3}
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hKdim : ∀ c ∈ K.faces, c.card ≤ 3)
    (A : SimplicialComplex ℝ V) (hAdim : ∀ c ∈ A.faces, c.card ≤ 2)
    {face old : Finset V} (hface : face ∈ K.faces) (hold : old ∈ K.faces)
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
  have hf3 := hKdim _ hface
  have ho3 := hKdim _ hold
  dsimp only
  cases boundary with
  | false =>
    have hplane : Module.finrank ℝ motion.plane.direction = 3 := motion.finrank_plane
    rw [hplane] at hrank
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro h
      cases h
    · intro h
      rcases h with h | h <;> omega
    · intro _
      omega
  | true =>
    have hplane : Module.finrank ℝ motion.plane.direction = 2 := motion.finrank_plane
    rw [hplane] at hrank
    have hf2 := hAdim _ (hmarked rfl).1
    have ho2 := hAdim _ (hmarked rfl).2
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro _
      omega
    · intro _
      omega
    · intro h
      cases h

end Geometry.OriginalPLTower
