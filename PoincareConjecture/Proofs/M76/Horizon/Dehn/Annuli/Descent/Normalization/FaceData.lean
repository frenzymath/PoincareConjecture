import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.RelativeFaceMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLChartHomeomorph

set_option autoImplicit false

open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

structure RelativeSurfaceState (t : Stage e S f r C) (K : SimplicialComplex ℝ V)
    (N : K.faces → Set t.Carrier) (R : Set M) (boundary : Set V) where
  map : V → t.Carrier
  original_PL : PolyhedralPLInCharts t.charts map K.space
  embedding : IsEmbedding (fun x : K.space ↦ map x)
  region : MapsTo map K.space (t.projection ⁻¹' R)
  proper : ∀ x ∈ K.space, map x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary
  retained : ∀ a : K.faces, MapsTo map (convexHull ℝ (a.val : Set V)) (N a)

structure RelativeFaceMotionData {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (j : V → t.Carrier)
    (Q : OpenPartialHomeomorph t.Carrier E) (B : OpenPartialHomeomorph s.Carrier E)
    (J : SimplicialComplex ℝ E) (N : K.faces → Set t.Carrier) (R : Set M) where
  source : SimplicialComplex ℝ E
  protectedSource : SimplicialComplex ℝ E
  targets : K₀.faces → SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  protected_finite : protectedSource.faces.Finite
  source_space : source.space = Q '' (j '' K₁.space ∩ Q.source) ∩ J.space
  protected_space : protectedSource.space = Q '' (j '' K₀.space ∩ Q.source) ∩ J.space
  targets_finite : ∀ a, (targets a).faces.Finite
  targets_space : ∀ a : K₀.faces, (targets a).space =
    B '' (((step.projection ∘ step.inclusion) ∘ j) ''
      convexHull ℝ (a.val : Set V) ∩ B.source) ∩ J.space
  targets_card : ∀ a b, b ∈ (targets a).faces → b.card ≤ a.val.card
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  subdivision : SimplicialComplex ℝ E
  freeComplex : SimplicialComplex ℝ E
  fixedComplex : SimplicialComplex ℝ E
  subdivision_finite : subdivision.faces.Finite
  subdivides : subdivision.IsSubdivision J
  free_le : freeComplex ≤ subdivision
  free_space : freeComplex.space = source.space
  fixed_le : fixedComplex ≤ freeComplex
  fixed_space : fixedComplex.space = protectedSource.space
  fixed_full : ∀ a ∈ freeComplex.faces,
    (∀ v ∈ a, v ∈ fixedComplex.vertices) → a ∈ fixedComplex.faces
  coordinates : PLCarrierMotion J.space protectedSource.space epsilon
  endpoint_affine : subdivision.AffineOnFaces (coordinates.map 1)
  endpointImage : SimplicialComplex ℝ E
  endpointImage_finite : endpointImage.faces.Finite
  endpointImage_space : endpointImage.space = coordinates.map 1 '' source.space
  position : ∀ a b, b ∈ freeComplex.faces → b ∉ fixedComplex.faces →
    ∀ c, c ∈ (targets a).faces →
      affineSpan ℝ (coordinates.map 1 '' (b : Set E) ∪ (c : Set E)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (coordinates.map 1 '' (b : Set E))))
          (convexHull ℝ (c : Set E))
  ambient : I → t.Carrier ≃ₜ t.Carrier
  continuous : Continuous (fun z : I × t.Carrier ↦ ambient z.1 z.2)
  continuous_inverse : Continuous (fun z : I × t.Carrier ↦ (ambient z.1).symm z.2)
  zero : ∀ x, ambient 0 x = x
  chart_formula : ∀ u, EqOn (ambient u) (Q.symm ∘ coordinates.map u ∘ Q) Q.source
  outside : ∀ u, EqOn (ambient u) id (Q.symm '' J.space)ᶜ
  prefix_fixed : ∀ u, EqOn (ambient u) id (j '' K₀.space)
  frontier : ∀ u, EqOn (ambient u) id (frontier (t.projection ⁻¹' R))
  region : ∀ u, (ambient u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  original_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid E
  inverse_PL : ∀ u k l, (t.charts k).symm.trans
    ((ambient u).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid E
  retained : ∀ u a, MapsTo (ambient u ∘ j) (convexHull ℝ (a.val : Set V)) (N a)

theorem Step.nonempty_relative_face_motion_data {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {N : K.faces → Set t.Carrier} {R : Set M} {boundary : Set V}
    (state : RelativeSurfaceState t K N R boundary)
    (face : Finset V) (hsource : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (Q : OpenPartialHomeomorph t.Carrier E) (B : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hJQ : J.space ⊆ Q.target) (hJB : J.space ⊆ B.target)
    (hfree : ∀ x ∈ convexHull ℝ (face : Set V),
      x ∉ K₀.space → Q (state.map x) ∈ interior J.space)
    (hinside : Q.source ⊆ interior (t.projection ⁻¹' R))
    (hN : ∀ a, IsOpen (N a)) :
    Nonempty (RelativeFaceMotionData step K K₀ K₁ state.map Q B J N R) := by
  obtain ⟨P, P₀, L, ε, hP, hP₀, hε, hPs, hP₀s, hL,
    K', T, T₀, H, hK', hK'J, hT, hTs, hT₀, hT₀s, hfull, hHaff,
    ⟨J', hJ', hJ's⟩, hHfaces, G, hG, hGinv, hzero, hformula, hout, hprefix, _,
    hfront, hregion, hGPL, hGinvPL, hkeep⟩ :=
    step.exists_relative_interior_face_motion K K₀ K₁ hK hK₀ hK₁ state.original_PL
      face hsource Q B hQ hB J hJ hcv hJQ hJB hfree R (frontier R) Subset.rfl
      hinside ∅ (by simp) N hN state.retained
  exact ⟨{
    source := P
    protectedSource := P₀
    targets := L
    source_finite := hP
    protected_finite := hP₀
    source_space := hPs
    protected_space := hP₀s
    targets_finite := fun a ↦ (hL a).1
    targets_space := fun a ↦ (hL a).2.1
    targets_card := fun a ↦ (hL a).2.2
    epsilon := ε
    epsilon_pos := hε
    subdivision := K'
    freeComplex := T
    fixedComplex := T₀
    subdivision_finite := hK'
    subdivides := hK'J
    free_le := hT
    free_space := hTs
    fixed_le := hT₀
    fixed_space := hT₀s
    fixed_full := hfull
    coordinates := H
    endpoint_affine := hHaff
    endpointImage := J'
    endpointImage_finite := hJ'
    endpointImage_space := hJ's
    position := hHfaces
    ambient := G
    continuous := hG
    continuous_inverse := hGinv
    zero := hzero
    chart_formula := hformula
    outside := hout
    prefix_fixed := hprefix
    frontier := hfront
    region := fun u ↦ (hregion u).1
    original_PL := hGPL
    inverse_PL := hGinvPL
    retained := hkeep }⟩

def RelativeSurfaceState.move {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    {N : K.faces → Set t.Carrier} {R : Set M} {boundary : Set V}
    (state : RelativeSurfaceState t K N R boundary)
    {Q : OpenPartialHomeomorph t.Carrier E} {B : OpenPartialHomeomorph s.Carrier E}
    {J : SimplicialComplex ℝ E}
    (motion : RelativeFaceMotionData step K K₀ K₁ state.map Q B J N R) :
    RelativeSurfaceState t K N R boundary where
  map := motion.ambient 1 ∘ state.map
  original_PL := state.original_PL.comp_chart_homeomorph K hK (motion.ambient 1)
    t.cover (motion.original_PL 1)
  embedding := (motion.ambient 1).isEmbedding.comp state.embedding
  region := by
    intro x hx
    change state.map x ∈ (motion.ambient 1) ⁻¹' (t.projection ⁻¹' R)
    rw [motion.region]
    exact state.region hx
  proper := by
    intro x hx
    have hfront : (motion.ambient 1) ⁻¹' frontier (t.projection ⁻¹' R) =
        frontier (t.projection ⁻¹' R) := by
      rw [(motion.ambient 1).preimage_frontier, motion.region]
    exact (Set.ext_iff.mp hfront (state.map x)).trans (state.proper x hx)
  retained := motion.retained 1

end Geometry.OriginalPLTower
