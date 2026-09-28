import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Cap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.SourceCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.RetainedCharts

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_circle_reduction
    {X ι κ : Type*} [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A₀ A₁ S₁ : Set P2} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (f₀ f₁ : P2 → X) (hS₁ : IsCompact S₁)
    (hf₀ : PolyhedralPLInCharts e f₀ J.space) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hf₀i : InjOn f₀ J.space) (hf₁i : InjOn f₁ S₁)
    (hf₀R : MapsTo f₀ J.space R)
    (hproper : ∀ x ∈ J.space, f₀ x ∈ frontier R ↔ x ∈ frontier J.space)
    (houter₀ : closure B₀.outer.inside ⊆ interior J.space)
    (houter₁ : closure B₁.outer.inside ⊆ S₁)
    (hf₁R : MapsTo f₁ (closure B₁.inner.inside) (interior R))
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hτR : MapsTo τ (_root_.Dehn.identityTube L d) (interior R))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hinnerB : Disjoint (f₁ '' closure B₁.inner.inside) (f₀ '' J.space))
    (hA : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ f₀ '' J.space ↔ z.1.2 = -z.1.1)
    (hperiod₀ : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
      (p : squareAnnulus L d), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), u) →
        f₀ (B₀.chart p) = τ ((u, -u), s))
    (hperiod₁ : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
      (p : squareAnnulus L d), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), u) →
        f₁ (B₁.chart p) = τ ((u, u), s))
    (pieces : κ → Set P2) (hclosed : ∀ i, IsClosed (pieces i))
    (hdis : Pairwise (fun i j => Disjoint (pieces i) (pieces j)))
    (hcover : ⋃ i, pieces i = J.space ∩ f₀ ⁻¹' (f₁ '' S₁))
    (hconn : ∀ i, IsConnected (pieces i)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k J.space ∧
      IsEmbedding (fun x : J.space => k x) ∧ MapsTo k J.space R ∧
      EqOn k f₀ (J.space \ B₀.outer.inside) ∧ EqOn k f₀ (frontier J.space) ∧
      (∀ x ∈ J.space, k x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      J.space ∩ k ⁻¹' (f₁ '' S₁) = (J.space ∩ f₀ ⁻¹' (f₁ '' S₁)) \ B₀.outer.inside ∧
      Nat.card (ConnectedComponents (J.space ∩ k ⁻¹' (f₁ '' S₁) : Set P2)) <
        Nat.card (ConnectedComponents (J.space ∩ f₀ ⁻¹' (f₁ '' S₁) : Set P2)) ∧
      ∀ (y : X) (boundary : Bool), y ∈ (f₁ '' S₁) ∩ (k '' J.space) →
        OriginalSurfacePairChart e (f₁ '' S₁) (f₀ '' J.space) y boundary →
        Nonempty (OriginalSurfacePairChart e (f₁ '' S₁) (k '' J.space) y boundary) := by
  classical
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hD := B₀.outer.isFinitePLBallPair_closed_inside B₀.outer_simplicial B₀.outer_injective
  have houterR : MapsTo f₀ (closure B₀.outer.inside) (interior R) := by
    intro x hx
    rw [←self_sdiff_frontier]
    exact ⟨hf₀R (interior_subset (houter₀ hx)),fun hh =>
      ((hproper x (interior_subset (houter₀ hx))).mp hh).2 (houter₀ hx)⟩
  obtain ⟨g,hg,hgi,hgR,hgr,hgA,hgB⟩ := exists_original_circle_removal_cap
    hR he hd hwidth B₀ B₁ f₀ f₁ (J.isCompact_space_of_finite hJ) hS₁
    hf₀ hf₁ hf₀i hf₁i (houter₀.trans interior_subset) houter₁ houterR hf₁R
    τ hτ hτR hfib hinnerB hA hB
    (fun p _ s hs hp => by
      simpa only [neg_neg] using (hperiod₀ s hs ⟨-d,le_rfl,by linarith⟩ p hp)) hperiod₁
  have hrim : f₀ '' B₀.outer.boundary ℝ = g '' B₀.outer.boundary ℝ :=
    (image_congr hgr).symm
  have hcontact : (g '' closure B₀.outer.inside) ∩
      (f₀ '' (J.space \ B₀.outer.inside)) = f₀ '' B₀.outer.boundary ℝ := by
    apply Subset.antisymm
    · rintro y ⟨⟨x,hx,rfl⟩,hy⟩
      have hxr := (hgB x hx).mp (image_mono sdiff_subset hy)
      exact ⟨x,hxr,(hgr hxr).symm⟩
    · rintro y ⟨x,hx,rfl⟩
      refine ⟨⟨x,hD.1 hx,hgr hx⟩,⟨x,⟨interior_subset (houter₀ (hD.1 hx)),?_⟩,rfl⟩⟩
      have hh : x ∈ frontier B₀.outer.inside :=
        (B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective).symm ▸ hx
      exact fun hin => hh.2 ((B₀.outer.isOpen_inside B₀.outer_simplicial
        B₀.outer_injective).interior_eq.symm ▸ hin)
  let p0 : squareAnnulus L d := ⟨annulusMap L (by linarith) ((0 : AddCircle (4 * L)),0),
    annulus_period_point_mem hd hwidth _ ⟨0,by linarith,by linarith⟩⟩
  let x : P2 := B₀.chart p0
  have hxclosed : x ∈ closure B₀.outer.inside :=
    (B₀.carrier.subset (B₀.chart p0).property).1
  have hxinside : x ∈ B₀.outer.inside := by
    rw [←B₀.outer.interior_closure_inside B₀.outer_simplicial B₀.outer_injective,
      ←self_sdiff_frontier]
    refine ⟨hxclosed,?_⟩
    rw [B₀.outer.frontier_closure_inside B₀.outer_simplicial B₀.outer_injective]
    intro hx
    have hh := (B₀.outer_depth p0).mp hx
    have ht : depth L (p0 : P2) = 0 := depth_annulusMap (by linarith)
      (by simp; linarith) _
    linarith
  have hxA : f₀ x ∈ f₁ '' S₁ := by
    have hv := hperiod₀ 0 ⟨le_rfl,by linarith⟩ ⟨0,by linarith,by linarith⟩ p0 rfl
    change f₀ x = τ ((0,-0),0) at hv
    rw [hv]
    apply (hA _ ?_).mpr (by norm_num)
    exact ⟨⟨⟨by linarith,by linarith⟩,⟨by simp; linarith,by simp; linarith⟩⟩,
      ⟨le_rfl,by linarith⟩⟩
  obtain ⟨k,hk,hki,hkeep,hfront,hdisk,himage,hsource,hcount⟩ :=
    exists_original_disk_replacement_with_count_decrease he.compatible J hJ B₀.outer
      B₀.outer_simplicial B₀.outer_injective houter₀ hf₀ hf₀i hD hg hgi hrim hcontact
      hgA pieces hclosed hdis hcover hconn
      ⟨x,⟨interior_subset (houter₀ hxclosed),hxA⟩,hxinside⟩
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp (J.isCompact_space_of_finite hJ)
  have hemb : IsEmbedding (fun x : J.space => k x) :=
    (hk.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hki x.property y.property hxy))).isEmbedding
  have hkR : MapsTo k J.space R := by
    intro x hx
    rcases himage.subset ⟨x,hx,rfl⟩ with ⟨y,hy,hyx⟩ | ⟨y,hy,hyx⟩
    · exact hyx ▸ hf₀R hy.1
    · exact hyx ▸ interior_subset (hgR hy)
  refine ⟨k,hk,hemb,hkR,hkeep,hfront,?_,hsource,hcount,?_⟩
  · intro x hx
    by_cases hD' : x ∈ closure B₀.outer.inside
    · have hkint : k x ∈ interior R := by
        obtain ⟨y,hy,hyx⟩ := hdisk.subset ⟨x,hD',rfl⟩
        exact hyx ▸ hgR hy
      exact ⟨fun h => (h.2 hkint).elim,fun h => (h.2 (houter₀ hD')).elim⟩
    · rw [hkeep ⟨hx,fun h => hD' (subset_closure h)⟩]
      exact hproper x hx
  · intro y boundary hy C
    have hold : f₀ '' J.space = f₀ '' (J.space \ B₀.outer.inside) ∪
        f₀ '' closure B₀.outer.inside := by
      rw [←image_union]
      congr 1
      apply Subset.antisymm
      · intro z hz
        by_cases hi : z ∈ B₀.outer.inside
        · exact Or.inr (subset_closure hi)
        · exact Or.inl ⟨hz,hi⟩
      · exact union_subset sdiff_subset (houter₀.trans interior_subset)
    have hseam : (f₀ '' (J.space \ B₀.outer.inside)) ∩
        (f₀ '' closure B₀.outer.inside) ⊆ g '' closure B₀.outer.inside := by
      rintro z ⟨⟨x,⟨hxJ,hxout⟩,rfl⟩,w,hw,hwx⟩
      have hwx' := hf₀i (interior_subset (houter₀ hw)) hxJ hwx
      subst w
      have hxr : x ∈ B₀.outer.boundary ℝ := by
        rw [←B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective]
        exact ⟨hw,fun hi => hxout (interior_subset hi)⟩
      exact ⟨x,hD.1 hxr,hgr hxr⟩
    exact C.exists_after_compact_replacement
      (hD.isCompact.image_of_continuousOn
        (hf₀.continuousOn.mono (houter₀.trans interior_subset))).isClosed
      (hD.isCompact.image_of_continuousOn hg.continuousOn).isClosed
      hold himage hseam hgA hy

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
