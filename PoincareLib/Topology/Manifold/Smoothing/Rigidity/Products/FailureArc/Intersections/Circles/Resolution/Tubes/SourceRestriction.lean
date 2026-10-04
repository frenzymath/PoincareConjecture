import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.LocalConstruction
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surgery.Retention.CrossingFamily

/-! # Isolate a compact paired circle from a mixed source double locus -/

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareMT.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finite_isolated_double_source
    {X : Type*} {f : P2 → X} {S C : Set P2}
    (hC : IsCompact C) (hCI : C ⊆ interior S)
    (hrest : IsClosed (doubleLocusOn f S \ C))
    (hpaired : ∀ x ∈ C, ∃ y ∈ C, f x = f y ∧ x ≠ y) :
    ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧ K.space ⊆ S ∧
      C ⊆ interior K.space ∧ doubleLocusOn f K.space = C := by
  obtain ⟨K,hK,hCK,hKS⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    hC (isOpen_interior.sdiff hrest) (fun x hx => ⟨hCI hx,fun hh => hh.2 hx⟩)
  have hsub : K.space ⊆ S := fun _ hx => interior_subset (hKS hx).1
  refine ⟨K,hK,hsub,hCK,Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hx,y,hy,hxy,hne⟩
    by_contra hxc
    exact (hKS hx).2 ⟨⟨hsub hx,y,hsub hy,hxy,hne⟩,hxc⟩
  · intro x hx
    obtain ⟨y,hy,hxy,hne⟩ := hpaired x hx
    exact ⟨interior_subset (hCK hx),y,interior_subset (hCK hy),hxy,hne⟩

theorem raw_crossings_on_isolated_source
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S T : Set P2} {R : Set X}
    (hS : IsCompact S) (hT : IsCompact T) (hTS : T ⊆ S)
    (hf : ContinuousOn f S) (hinterior : doubleLocusOn f T ⊆ interior T)
    (hunique : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y)) :
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f T R x y) := by
  classical
  have hp : ∀ x : doubleLocusOn f S, ∃ y : doubleLocusOn f S,
      f x = f y ∧ (x : P2) ≠ y := by
    rintro ⟨x,hx,y,hy,hxy,hne⟩
    exact ⟨⟨y,hy,x,hx,hxy.symm,hne.symm⟩,hxy,hne⟩
  let p := fun x => Classical.choose (hp x)
  have hpu : ∀ (x : doubleLocusOn f S) (y : P2), y ∈ S →
      f x = f y → (x : P2) ≠ y → y = (p x : P2) := by
    intro x y hy hxy hne
    exact hunique x x.property.1 y hy (p x) (p x).property.1 hne
      (Classical.choose_spec (hp x)).2 hxy (Classical.choose_spec (hp x)).1
  have hc := raw_source_crossings_of_retained_open_copy hS hT
    (interior_subset.trans hTS) interior_subset
    (isOpen_interior.preimage continuous_subtype_val)
    (isOpen_interior.preimage continuous_subtype_val)
    hf (hf.mono hTS) (Homeomorph.refl (interior T)) (fun _ => rfl)
    p hpu hinterior (fun x hx y hy heq hne => hcross x hx y hy hne heq)
  exact fun x hx y hy hne heq => hc x hx y hy heq hne

theorem nonempty_circle_decomposition_on_isolated_source
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S C : Set P2} {R : Set X}
    (he : PLDomain e R) (hS : IsCompact S) (hf : PolyhedralPLInCharts e f S)
    (hfR : MapsTo f S R) (hC : IsCompact C) (hCI : C ⊆ interior S)
    (hCR : MapsTo f C (interior R)) (hrest : IsClosed (doubleLocusOn f S \ C))
    (hpaired : ∀ x ∈ C, ∃ y ∈ C, f x = f y ∧ x ≠ y)
    (hunique : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z)
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y)) :
    ∃ (K : SimplicialComplex ℝ P2) (_old : SourceCircleDecomposition f K.space),
      K.faces.Finite ∧ K.space ⊆ S ∧ C ⊆ interior K.space ∧
      doubleLocusOn f K.space = C ∧ PolyhedralPLInCharts e f K.space ∧
      (∀ x ∈ K.space, ∀ y ∈ K.space, x ≠ y → f x = f y →
        Nonempty (RawSourceCrossing e f K.space R x y)) := by
  obtain ⟨K,hK,hKS,hCK,hdouble⟩ := exists_finite_isolated_double_source hC hCI hrest hpaired
  have hfK := hf.restrict_finite K hK hKS
  have hcK := raw_crossings_on_isolated_source hS (K.isCompact_space_of_finite hK)
    hKS hf.continuousOn (hdouble ▸ hCK) hunique hcross
  obtain ⟨old⟩ := nonempty_sourceCircleDecomposition he.compatible K hK hfK
    (fun _ hx => hfR (hKS hx)) (hdouble ▸ hC.isClosed) (hdouble ▸ hCR) hcK
    (fun x hx y hy z hz => hunique x (hKS hx) y (hKS hy) z (hKS hz))
  exact ⟨K,old,hK,hKS,hCK,hdouble,hfK,hcK⟩

end PoincareMT.M76.Dehn.Annuli.CircleResolution
