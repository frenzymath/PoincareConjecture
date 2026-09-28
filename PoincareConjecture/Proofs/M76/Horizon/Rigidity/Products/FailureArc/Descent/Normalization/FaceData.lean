import PoincareConjecture.Proofs.M76.Dehn.OriginalPLSuccessor
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion

set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

structure MarkedSurfaceMotionData {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (j : V → t.Carrier)
    (Q : OpenPartialHomeomorph t.Carrier E)
    (B : OpenPartialHomeomorph s.Carrier E) (J : SimplicialComplex ℝ E)
    (U : K.faces → Set t.Carrier) (R Fmark : Set M) (boundary : Bool) where
  support : SimplicialComplex ℝ E
  source : SimplicialComplex ℝ E
  fixedSource : SimplicialComplex ℝ E
  targets : K₀.faces → SimplicialComplex ℝ E
  plane : AffineSubspace ℝ E
  support_finite : support.faces.Finite
  support_convex : Convex ℝ support.space
  support_subset : support.space ⊆ J.space
  support_upper : support.space ⊆ Q.target
  support_lower : support.space ⊆ B.target
  source_finite : source.faces.Finite
  protected_finite : fixedSource.faces.Finite
  source_space : source.space = Q '' (j '' K₁.space ∩ Q.source) ∩ support.space
  protected_space : fixedSource.space = Q '' (j '' K₀.space ∩ Q.source) ∩ support.space
  protected_subset : fixedSource.space ⊆ source.space
  source_subset : source.space ⊆ support.space
  active_supported : ∀ x ∈ K₁.space,
    x ∉ K₀.space → Q (j x) ∈ interior support.space
  frontier_protected : source.space ∩ frontier support.space ⊆ fixedSource.space
  targets_finite : ∀ a, (targets a).faces.Finite
  targets_space : ∀ a : K₀.faces,
    (targets a).space = B '' (((step.projection ∘ step.inclusion) ∘ j) ''
      convexHull ℝ (a.val : Set V) ∩ B.source) ∩ support.space
  targets_card : ∀ a b, b ∈ (targets a).faces → b.card ≤ a.val.card
  subdivision : SimplicialComplex ℝ E
  freeComplex : SimplicialComplex ℝ E
  fixedComplex : SimplicialComplex ℝ E
  subdivision_finite : subdivision.faces.Finite
  subdivides : subdivision.IsSubdivision support
  free_le : freeComplex ≤ subdivision
  free_space : freeComplex.space = source.space
  fixed_le : fixedComplex ≤ freeComplex
  fixed_space : fixedComplex.space = fixedSource.space
  fixed_full : ∀ a ∈ freeComplex.faces,
    (∀ v ∈ a, v ∈ fixedComplex.vertices) → a ∈ fixedComplex.faces
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  coordinates : PLCarrierMotion support.space fixedSource.space epsilon
  endpoint_affine : subdivision.AffineOnFaces (coordinates.map 1)
  endpointImage : SimplicialComplex ℝ E
  endpointImage_finite : endpointImage.faces.Finite
  endpointImage_space : endpointImage.space = coordinates.map 1 '' source.space
  position : ∀ a b, b ∈ freeComplex.faces → b ∉ fixedComplex.faces →
    ∀ c, c ∈ (targets a).faces →
      affineSpan ℝ (coordinates.map 1 '' (b : Set E) ∪ (c : Set E)) = plane ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (coordinates.map 1 '' (b : Set E))))
          (convexHull ℝ (c : Set E))
  boundary_support : boundary = true → support.space = J.space
  boundary_plane : boundary = true →
    ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
      (plane : Set E) = {z | ell z = 0} ∧ plane.direction = ell.toAffineMap.linear.ker ∧
      source.space ⊆ plane ∧ (∀ a, (targets a).space ⊆ plane) ∧
      ∀ a z, ell (coordinates.map a z) = ell z
  interior_plane : boundary = false → plane = ⊤
  ambient : I → t.Carrier ≃ₜ t.Carrier
  continuous_ambient : Continuous (fun z : I × t.Carrier => ambient z.1 z.2)
  continuous_inverse : Continuous (fun z : I × t.Carrier => (ambient z.1).symm z.2)
  zero : ∀ x, ambient 0 x = x
  chart_formula : ∀ a, EqOn (ambient a) (Q.symm ∘ coordinates.map a ∘ Q) Q.source
  exterior : ∀ a, EqOn (ambient a) id (Q.symm '' support.space)ᶜ
  prefix_fixed : ∀ a, EqOn (ambient a) id (j '' K₀.space)
  region : ∀ a, (ambient a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  mark : ∀ a, (ambient a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark
  frontier_fixed : boundary = false →
    ∀ a, EqOn (ambient a) id (frontier (t.projection ⁻¹' R))
  original_PL : ∀ a k l, (t.charts k).symm.trans
    ((ambient a).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid E
  original_inverse_PL : ∀ a k l, (t.charts k).symm.trans
    ((ambient a).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid E
  retained : ∀ a b, MapsTo (ambient a ∘ j) (convexHull ℝ (b.val : Set V)) (U b)

end Geometry.OriginalPLTower
