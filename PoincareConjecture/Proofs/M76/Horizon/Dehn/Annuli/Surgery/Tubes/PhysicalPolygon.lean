import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.SelfPairedSourceCircle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.EndpointLoopPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → X} {S : Set E}

theorem SourceCircleDecomposition.exists_selfpaired_physical_polygon
    (M : SourceCircleDecomposition f S)
    (i : M.Index) (hself : M.mate i = i)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y) (hF : FinitePiecewiseAffineOn (F ∘ f) (M.pieces i))
    (hFi : InjOn F (f '' M.pieces i)) :
    ∃ (N : ℕ) (Q : Polygon Y (N + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (F ∘ f) '' M.pieces i := by
  obtain ⟨a, b, U, V, alpha, beta, _, _, _, hcover, _, halpha, _, _, _, _, _, _, _,
    hfib, himage, _⟩ := M.exists_selfpaired_twofold_source_arcs i hself
  obtain ⟨l, hl, hlval⟩ := halpha
  have hU : U ⊆ M.pieces i := subset_union_left.trans hcover.subset
  have hlmaps : MapsTo l (Icc (0 : ℝ) 1) (M.pieces i) := by
    intro t ht
    rw [← hlval ⟨t, ht⟩]
    exact hU (alpha ⟨t, ht⟩).property
  have hloopPL : FinitePiecewiseAffineOn ((F ∘ f) ∘ l) (Icc (0 : ℝ) 1) :=
    hF.comp hl hlmaps
  have hloopFib : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ((F ∘ f) ∘ l) x = ((F ∘ f) ∘ l) y ↔
        x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
    intro x hx y hy
    have hFiff : F (f (l x)) = F (f (l y)) ↔ f (l x) = f (l y) :=
      ⟨fun h => hFi (mem_image_of_mem f (hlmaps hx))
        (mem_image_of_mem f (hlmaps hy)) h, congrArg F⟩
    change F (f (l x)) = F (f (l y)) ↔ _
    rw [hFiff, ← hlval ⟨x, hx⟩, ← hlval ⟨y, hy⟩, hfib]
    simp only [Subtype.ext_iff]
    rfl
  obtain ⟨N, Q, hQi, hQs, hQb⟩ := exists_polygon_of_endpoint_loop hloopPL hloopFib
  refine ⟨N, Q, hQi, hQs, hQb.trans ?_⟩
  have hlimage : l '' Icc (0 : ℝ) 1 = U := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [← hlval ⟨t, ht⟩]
      exact (alpha ⟨t, ht⟩).property
    · intro hx
      refine ⟨alpha.symm ⟨x, hx⟩, (alpha.symm ⟨x, hx⟩).property, ?_⟩
      rw [← hlval, alpha.apply_symm_apply]
  rw [image_comp (F ∘ f) l, hlimage, image_comp F f, himage, image_comp F f]

theorem SourceCircleDecomposition.injOn_piece_of_mate_ne
    (M : SourceCircleDecomposition f S) (i : M.Index) (hne : M.mate i ≠ i) :
    InjOn f (M.pieces i) := by
  intro x hx y hy hxy
  by_contra hne'
  have hxG := M.space.symm.subset (M.piece_subset_double i hx)
  have heq := M.unique ⟨x, hxG⟩ y (M.piece_subset_source i hy) hne' hxy
  have hym : y ∈ M.pieces (M.mate i) := heq.symm ▸
    (M.partner_component i ⟨x, hxG⟩).mp hx
  exact disjoint_left.mp (M.disjoint hne) hym hy

theorem SourceCircleDecomposition.exists_physical_polygon
    (M : SourceCircleDecomposition f S) (i : M.Index)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : X → F) (hg : FinitePiecewiseAffineOn (g ∘ f) (M.pieces i))
    (hgi : InjOn g (f '' M.pieces i)) :
    ∃ (n : ℕ) (P : Polygon F (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (g ∘ f) '' M.pieces i := by
  classical
  by_cases hself : M.mate i = i
  · exact M.exists_selfpaired_physical_polygon i hself g hg hgi
  · exact (M.polygon i).exists_polygon_finitePL_image (M.model i).2.1 (M.model i).1
      hg Subset.rfl (fun _ hx _ hy hxy ↦ M.injOn_piece_of_mate_ne i hself hx hy
        (hgi (mem_image_of_mem f hx) (mem_image_of_mem f hy) hxy))

end PoincareConjecture.M76.Dehn.Annuli
