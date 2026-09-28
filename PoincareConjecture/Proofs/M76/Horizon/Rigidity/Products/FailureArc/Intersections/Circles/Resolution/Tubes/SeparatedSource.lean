import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SourceCopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairIsolation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.CopiedCrossings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.CopiedFibers



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

structure SeparatedCircleSource
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (f₀ f₁ : P2 → X)
    (S₀ S₁ C₀ C₁ : Set P2) (R : Set X) where
  shift : P2 ≃ᴬ[ℝ] P2
  first : SimplicialComplex ℝ P2
  second : SimplicialComplex ℝ P2
  source : SimplicialComplex ℝ P2
  map : P2 → X
  first_finite : first.faces.Finite
  second_finite : second.faces.Finite
  source_finite : source.faces.Finite
  first_subset : first.space ⊆ interior S₀
  second_subset : second.space ⊆ interior S₁
  first_selected : C₀ ⊆ interior first.space
  second_selected : C₁ ⊆ interior second.space
  disjoint : Disjoint first.space (shift '' second.space)
  source_space : source.space = first.space ∪ shift '' second.space
  first_value : EqOn map f₀ first.space
  second_value : ∀ x ∈ second.space, map (shift x) = f₁ x
  map_PL : PolyhedralPLInCharts e map source.space
  map_region : MapsTo map source.space R
  first_injective : InjOn map first.space
  second_injective : InjOn map (shift '' second.space)
  double_space : doubleLocusOn map source.space = C₀ ∪ shift '' C₁
  double_interior : doubleLocusOn map source.space ⊆ interior source.space
  double_region : MapsTo map (doubleLocusOn map source.space) (interior R)
  crossings : ∀ x ∈ source.space, ∀ y ∈ source.space, x ≠ y → map x = map y →
    Nonempty (RawSourceCrossing e map source.space R x y)
  decomposition : SourceCircleDecomposition map source.space

theorem nonempty_separatedCircleSource
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {f₀ f₁ : P2 → X} {S₀ S₁ C₀ C₁ : Set P2}
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ S₀ R) (hf₁R : MapsTo f₁ S₁ R)
    (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁)
    (hC₀S : C₀ ⊆ interior S₀) (hC₁S : C₁ ⊆ interior S₁)
    (himage : f₀ '' C₀ = f₁ '' C₁)
    (hCR : MapsTo f₀ C₀ (interior R))
    (hrest₀ : IsClosed ({x | x ∈ S₀ ∧ f₀ x ∈ f₁ '' S₁} \ C₀))
    (hrest₁ : IsClosed ({y | y ∈ S₁ ∧ f₁ y ∈ f₀ '' S₀} \ C₁))
    (hcharts : ∀ x ∈ C₀,
      Nonempty (OriginalSurfacePairChart e (f₀ '' S₀) (f₁ '' S₁) (f₀ x) false)) :
    Nonempty (SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R) := by
  obtain ⟨K₀,K₁,hK₀,hK₁,hKS₀,hKS₁,hCK₀,hCK₁,htrace₀,htrace₁⟩ :=
    exists_isolated_pair_sources hC₀ hC₁ hC₀S hC₁S himage hrest₀ hrest₁
  have hsub₀ := hKS₀.trans interior_subset
  have hsub₁ := hKS₁.trans interior_subset
  have hfK₀ := hf₀.restrict_finite K₀ hK₀ hsub₀
  have hfK₁ := hf₁.restrict_finite K₁ hK₁ hsub₁
  obtain ⟨a,L,f,hdis,hL,hLs,hf,hkeep₀,hkeep₁⟩ :=
    exists_disjoint_planar_source_map he.compatible K₀ K₁ hK₀ hK₁ f₀ f₁ hfK₀ hfK₁
  obtain ⟨hfi₀,hfi₁,hdouble⟩ := copied_pair_double_locus a hdis
    (hf₀i.mono hsub₀) (hf₁i.mono hsub₁) hkeep₀ hkeep₁ htrace₀ htrace₁
  have hdoubleL : doubleLocusOn f L.space = C₀ ∪ a '' C₁ := hLs ▸ hdouble
  have hDinterior : doubleLocusOn f L.space ⊆ interior L.space := by
    rw [hdoubleL,hLs]
    apply union_subset
    · exact hCK₀.trans (interior_mono subset_union_left)
    · rintro _ ⟨x,hx,rfl⟩
      apply interior_mono subset_union_right
      exact a.toHomeomorph.isOpenMap.image_interior_subset K₁.space ⟨x,hCK₁ hx,rfl⟩
  have hDregion : MapsTo f (doubleLocusOn f L.space) (interior R) := by
    intro x hx
    rcases hdoubleL.subset hx with hx | hx
    · rw [hkeep₀ (interior_subset (hCK₀ hx))]
      exact hCR hx
    · obtain ⟨y,hy,rfl⟩ := hx
      rw [hkeep₁ y (interior_subset (hCK₁ hy))]
      obtain ⟨z,hz,hzy⟩ := himage.symm.subset ⟨y,hy,rfl⟩
      exact hzy ▸ hCR hz
  have hregion : MapsTo f L.space R := by
    intro x hx
    rcases hLs.subset hx with hx | hx
    · rw [hkeep₀ hx]
      exact hf₀R (hsub₀ hx)
    · obtain ⟨y,hy,rfl⟩ := hx
      rw [hkeep₁ y hy]
      exact hf₁R (hsub₁ hy)
  have hcross : ∀ x ∈ L.space, ∀ y ∈ L.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f L.space R x y) := by
    rw [hLs]
    exact copied_pair_raw_crossings a hS₀ hS₁
      (K₀.isCompact_space_of_finite hK₀) (K₁.isCompact_space_of_finite hK₁)
      hsub₀ hsub₁ hf₀.continuousOn hf₁.continuousOn hf₀i hf₁i hdis
      (hLs ▸ hf.continuousOn) hkeep₀ hkeep₁ htrace₀ htrace₁ hCK₀ hCK₁ hCR hcharts
  have hclosed : IsClosed (doubleLocusOn f L.space) := by
    rw [hdoubleL]
    exact (hC₀.union (hC₁.image a.continuous)).isClosed
  obtain ⟨old⟩ := nonempty_sourceCircleDecomposition he.compatible L hL hf hregion
    hclosed hDregion hcross (by
      intro x hx y hy z hz hxy hxz hfxy hfxz
      exact disjoint_source_pair_unique hdis hfi₀ hfi₁
        (hLs.subset hx) (hLs.subset hy) (hLs.subset hz) hxy hxz hfxy hfxz)
  exact ⟨{
    shift := a, first := K₀, second := K₁, source := L, map := f,
    first_finite := hK₀, second_finite := hK₁, source_finite := hL,
    first_subset := hKS₀, second_subset := hKS₁,
    first_selected := hCK₀, second_selected := hCK₁,
    disjoint := hdis, source_space := hLs, first_value := hkeep₀, second_value := hkeep₁,
    map_PL := hf, map_region := hregion, first_injective := hfi₀, second_injective := hfi₁,
    double_space := hdoubleL, double_interior := hDinterior, double_region := hDregion,
    crossings := hcross, decomposition := old }⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
