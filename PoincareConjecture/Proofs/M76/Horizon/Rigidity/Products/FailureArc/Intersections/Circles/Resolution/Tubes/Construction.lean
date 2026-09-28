import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SynchronizedCollars
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SelectedTube

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem nonempty_synchronizedCircleCollars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {f₀ f₁ : P2 → X} {S₀ S₁ C₀ C₁ : Set P2}
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ S₀ R) (hf₁R : MapsTo f₁ S₁ R)
    (hC₀ : IsCompact C₀) (hC₁ : IsCompact C₁) (hc₀ : IsConnected C₀)
    (hC₀S : C₀ ⊆ interior S₀) (hC₁S : C₁ ⊆ interior S₁)
    (himage : f₀ '' C₀ = f₁ '' C₁) (hCR : MapsTo f₀ C₀ (interior R))
    (hrest₀ : IsClosed ({x | x ∈ S₀ ∧ f₀ x ∈ f₁ '' S₁} \ C₀))
    (hrest₁ : IsClosed ({y | y ∈ S₁ ∧ f₁ y ∈ f₀ '' S₀} \ C₁))
    (hcharts : ∀ x ∈ C₀,
      Nonempty (OriginalSurfacePairChart e (f₀ '' S₀) (f₁ '' S₁) (f₀ x) false))
    {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) :
    Nonempty (SynchronizedCircleCollars e f₀ f₁ S₀ S₁ C₀ C₁ R L d) := by
  obtain ⟨D⟩ := nonempty_separatedCircleSource he hS₀ hS₁ hf₀ hf₁ hf₀i hf₁i
    hf₀R hf₁R hC₀ hC₁ hC₀S hC₁S himage hCR hrest₀ hrest₁ hcharts
  obtain ⟨i,T,hi,hmi,hwhole₀,hwhole₁⟩ := D.exists_selected_identity_tube he hS₀ hS₁
    hf₀.continuousOn hf₁.continuousOn hf₀i hf₁i hC₀ hC₁ hc₀ himage hd hwidth
  exact D.nonempty_synchronizedCollars T hi hmi hwhole₀ hwhole₁

theorem SynchronizedCircleCollars.disk_containment
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X} {L d : ℝ}
    (T : SynchronizedCircleCollars e f₀ f₁ S₀ S₁ C₀ C₁ R L d)
    {n m : ℕ} (P₀ : Polygon P2 (n + 3)) (P₁ : Polygon P2 (m + 3))
    (hP₀ : P₀.HasSimplicialEdges) (hP₀i : Function.Injective P₀)
    (hP₁ : P₁.HasSimplicialEdges) (hP₁i : Function.Injective P₁)
    (hbound₀ : P₀.boundary ℝ = C₀) (hbound₁ : P₁.boundary ℝ = C₁)
    (hinside₀ : closure P₀.inside ⊆ interior S₀)
    (hinside₁ : closure P₁.inside ⊆ interior S₁)
    (havoid : Disjoint P₁.inside (S₁ ∩ f₁ ⁻¹' (f₀ '' S₀))) :
    closure T.collar₀.outer.inside ⊆ interior S₀ ∧
      closure T.collar₁.outer.inside ⊆ interior S₁ ∧
      Disjoint (f₁ '' closure T.collar₁.inner.inside) (f₀ '' S₀) := by
  obtain ⟨_,houter₀⟩ := oriented_collar_middle_disk T.depth_pos T.width_small
    T.collar₀ P₀ hP₀ hP₀i (T.middle₀.trans hbound₀.symm)
  obtain ⟨hinner₁,houter₁⟩ := oriented_collar_middle_disk T.depth_pos T.width_small
    T.collar₁ P₁ hP₁ hP₁i (T.middle₁.trans hbound₁.symm)
  refine ⟨houter₀.trans (union_subset hinside₀ T.source₀_subset),
    houter₁.trans (union_subset hinside₁ T.source₁_subset),?_⟩
  apply disjoint_left.mpr
  rintro y ⟨x,hx,rfl⟩ hy
  have hxP := hinner₁ hx
  exact disjoint_left.mp havoid hxP ⟨interior_subset (hinside₁ (subset_closure hxP)),hy⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
