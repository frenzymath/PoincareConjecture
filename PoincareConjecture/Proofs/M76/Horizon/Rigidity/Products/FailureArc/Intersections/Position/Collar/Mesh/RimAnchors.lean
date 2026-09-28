import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Parameters.Phases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Parameters.BoundaryContacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Frontier
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_source_rim_anchors_outside_target
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {mark : Bool → Set X}
    (Source K : SimplicialComplex ℝ P2) (hSource : Source.faces.Finite) (hK : K.faces.Finite)
    (hSources : Source.space = Ann)
    {f g : P2 → X} (hf : ContinuousOn f Source.space) (hfi : InjOn f Source.space)
    (hg : ContinuousOn g K.space)
    (hproper : ∀ x ∈ Source.space, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hmark : ∀ b z, f (annulusRimPoint b z) ∈ mark b)
    (hboundary : ∀ x ∈ K.space, g x ∈ frontier R → g x ∈ f '' Source.space →
      ∃ C : OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    ∃ a : Bool → X,
      (∀ b, a b ∈ mark b) ∧ (∀ b, a b ∈ f '' Source.space ∩ frontier R) ∧
      Disjoint (range a) (g '' K.space) ∧ IsClosed (range a) := by
  classical
  let Contact := (f '' Source.space ∩ g '' K.space) ∩ frontier R
  have hS : IsClosed (f '' Source.space) :=
    ((Source.isCompact_space_of_finite hSource).image_of_continuousOn hf).isClosed
  have hcompact : IsCompact Contact :=
    (((K.isCompact_space_of_finite hK).image_of_continuousOn hg).inter_left hS).inter_right
      isClosed_frontier
  have hfinite : Contact.Finite := finite_boundary_contacts_of_pair_charts hcompact (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy.1.2
    obtain ⟨C, hC⟩ := hboundary x hx hy.2 hy.1.1
    exact ⟨C, C.frontier_iff_of_region_halfspace hC⟩)
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Infinite (Ico (0 : ℝ) (0 + 4 * 8)) := Ico.infinite (by norm_num)
  let : Infinite Circle := Infinite.of_injective (AddCircle.equivIco (4 * (8 : ℝ)) 0).symm
    (AddCircle.equivIco (4 * (8 : ℝ)) 0).symm.injective
  have hrimSource (b : Bool) (z : Circle) :
      (annulusRimPoint b z : P2) ∈ Source.space := hSources.symm.subset (annulusRimPoint b z).property
  have hinj (b : Bool) : Function.Injective (fun z : Circle => f (annulusRimPoint b z)) := by
    intro z w h
    exact injective_planar_annulus_rim b (Subtype.ext (hfi (hrimSource b z) (hrimSource b w) h))
  have hex (b : Bool) : ∃ z : Circle, f (annulusRimPoint b z) ∉ Contact := by
    obtain ⟨z, _, hz⟩ := (Set.infinite_univ (α := Circle)).exists_notMem_finite
      (hfinite.preimage (hinj b).injOn)
    exact ⟨z, hz⟩
  choose z hz using hex
  let a (b : Bool) := f (annulusRimPoint b (z b))
  have ha (b : Bool) : a b ∈ f '' Source.space ∩ frontier R :=
    ⟨mem_image_of_mem f (hrimSource b (z b)),
      (hproper _ (hrimSource b (z b))).mpr (annulusRimPoint_mem_frontier b (z b))⟩
  refine ⟨a, fun b => hmark b (z b), ha, disjoint_left.mpr ?_, (Set.finite_range a).isClosed⟩
  rintro y ⟨b, rfl⟩ hy
  exact hz b ⟨⟨(ha b).1, hy⟩, (ha b).2⟩

end PoincareConjecture.M76
