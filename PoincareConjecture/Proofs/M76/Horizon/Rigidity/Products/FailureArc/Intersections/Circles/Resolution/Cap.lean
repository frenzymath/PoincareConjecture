import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.ExteriorAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.RetainedCore
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.OriginalSphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.FiniteCapPush



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_circle_removal_cap
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (hR : IsCompact R) (he : PLDomain e R)
    {A₀ A₁ S₀ S₁ : Set P2} {L d : ℝ} (hd : 0 < d) (hwidth : 4 * d < L)
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (f₀ f₁ : P2 → X) (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀ : PolyhedralPLInCharts e f₀ S₀) (hf₁ : PolyhedralPLInCharts e f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (houter₀ : closure B₀.outer.inside ⊆ S₀)
    (houter₁ : closure B₁.outer.inside ⊆ S₁)
    (hf₀R : MapsTo f₀ (closure B₀.outer.inside) (interior R))
    (hf₁R : MapsTo f₁ (closure B₁.inner.inside) (interior R))
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (_root_.Dehn.identityTube L d))
    (hτR : MapsTo τ (_root_.Dehn.identityTube L d) (interior R))
    (hfib : ∀ z ∈ _root_.Dehn.identityTube L d, ∀ w ∈ _root_.Dehn.identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hinnerB : Disjoint (f₁ '' closure B₁.inner.inside) (f₀ '' S₀))
    (hA : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1)
    (hB : ∀ z ∈ _root_.Dehn.identityTube L d, τ z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1)
    (houter : ∀ p : squareAnnulus L d, depth L p = -d →
      ∀ s ∈ Icc 0 (4 * L), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), -d) →
        f₀ (B₀.chart p) = τ ((-d, d), s))
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
      (p : squareAnnulus L d), (p : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), u) →
        f₁ (B₁.chart p) = τ ((u, u), s)) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k (closure B₀.outer.inside) ∧
      InjOn k (closure B₀.outer.inside) ∧ MapsTo k (closure B₀.outer.inside) (interior R) ∧
      EqOn k f₀ (B₀.outer.boundary ℝ) ∧
      Disjoint (k '' closure B₀.outer.inside) (f₁ '' S₁) ∧
      (∀ x ∈ closure B₀.outer.inside, k x ∈ f₀ '' S₀ ↔ x ∈ B₀.outer.boundary ℝ) := by
  classical
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have hD₀ := B₀.outer.isFinitePLBallPair_closed_inside B₀.outer_simplicial B₀.outer_injective
  have hD₁ := B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective
  have hinner₁ : closure B₁.inner.inside ⊆ S₁ :=
    B₁.nested.trans (subset_closure.trans houter₁)
  obtain ⟨K₀, _, hK₀, hKs₀, _, _⟩ := hD₀.exists_finite_carrier_and_rim_complexes
  obtain ⟨K₁, _, hK₁, hKs₁, _, _⟩ := hD₁.exists_finite_carrier_and_rim_complexes
  have hf₀D : PolyhedralPLInCharts e f₀ (closure B₀.outer.inside) :=
    hKs₀ ▸ hf₀.restrict_finite K₀ hK₀ (hKs₀.subset.trans houter₀)
  have hf₁D : PolyhedralPLInCharts e f₁ (closure B₁.inner.inside) :=
    hKs₁ ▸ hf₁.restrict_finite K₁ hK₁ (hKs₁.subset.trans hinner₁)
  obtain ⟨v, hv, hve, hkeep, hcapA, hcapB, himage⟩ :=
    exists_original_circle_cup e he.compatible hd hwidth B₀ B₁ f₀ f₁ hf₁D
      (hf₁i.mono hinner₁) τ hτ hfib (image_mono hinner₁) hinnerB hA hB houter
      (fun p _ s hs hp => hperiod s hs ⟨d, by linarith, le_rfl⟩ p hp)
  have hvi : InjOn v (closure B₀.outer.inside) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hve.injective (show
      (fun z : closure B₀.outer.inside => v z) ⟨x,hx⟩ =
      (fun z : closure B₀.outer.inside => v z) ⟨y,hy⟩ from hxy))
  have hrim : v '' B₀.outer.boundary ℝ = f₀ '' B₀.outer.boundary ℝ := image_congr hkeep
  have hinter : (v '' closure B₀.outer.inside) ∩ (f₀ '' closure B₀.outer.inside) =
      v '' B₀.outer.boundary ℝ := by
    rw [hrim]
    apply Subset.antisymm
    · exact fun _ hy => hcapB.subset ⟨hy.1, image_mono houter₀ hy.2⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x,hD₀.1 hx,hkeep hx⟩,⟨x,hD₀.1 hx,rfl⟩⟩
  obtain ⟨sphere⟩ := nonempty_original_sphere_of_disk_union he.compatible hD₀ hD₀
    hv hf₀D hvi (hf₀i.mono houter₀) hrim hinter
  let S := v '' closure B₀.outer.inside ∪ f₀ '' closure B₀.outer.inside
  have hvR : MapsTo v (closure B₀.outer.inside) (interior R) := by
    intro x hx
    rcases himage.subset ⟨x,hx,rfl⟩ with h | h
    · obtain ⟨y,hy,hyx⟩ := h
      exact hyx ▸ hf₁R hy
    · obtain ⟨z,hz,hzx⟩ := h
      have hzT : z ∈ _root_.Dehn.identityTube L d :=
        ⟨⟨hz.1.1, by simpa only [mem_singleton_iff.mp hz.1.2] using
          (show d ∈ Icc (-d) d from ⟨by linarith,le_rfl⟩)⟩,hz.2⟩
      exact hzx ▸ hτR hzT
  have hSR : S ⊆ interior R := union_subset (image_subset_iff.mpr hvR)
    (image_subset_iff.mpr hf₀R)
  have hCS : v '' closure B₀.outer.inside ⊆ S := subset_union_left
  have hSCB : S ⊆ v '' closure B₀.outer.inside ∪ f₀ '' S₀ :=
    union_subset_union_right _ (image_mono houter₀)
  obtain ⟨p,hp,hproper,hpzero,hpperiod,_⟩ := exists_cup_exterior_annulus
    hd hwidth (show 0 < d / 2 by linarith) (show d / 2 < d by linarith)
    B₁ f₁ (hf₁.continuousOn.mono houter₁) (hf₁i.mono houter₁) τ
    (A := f₁ '' S₁) (B := f₀ '' S₀)
    (fun x hx => ⟨x,houter₁ hx,rfl⟩) hB hcapA hCS hSCB hperiod
  obtain ⟨Z,hZ,hcupZ,hcover⟩ := exists_cup_retained_core
    hd hwidth (show 0 < d / 2 by linarith) (show d / 2 < d by linarith)
    B₁ f₁ hS₁ hf₁.continuousOn hf₁i houter₁ τ hcapA hCS hperiod p hpperiod
  have hrimA : Disjoint (v '' B₀.outer.boundary ℝ) (f₁ '' S₁) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ hy
    exact Set.disjoint_left.mp hinnerB (hcapA.subset ⟨⟨x,hD₀.1 hx,rfl⟩,hy⟩)
      ⟨x,houter₀ (hD₀.1 hx),(hkeep hx).symm⟩
  have hvB (x : P2) (hx : x ∈ closure B₀.outer.inside) :
      v x ∈ f₀ '' S₀ ↔ x ∈ B₀.outer.boundary ℝ := by
    constructor
    · intro hh
      obtain ⟨y,hy,hyx⟩ := hcapB.subset ⟨⟨x,hx,rfl⟩,hh⟩
      have hxy := hvi (hD₀.1 hy) hx ((hkeep hy).trans hyx)
      exact hxy ▸ hy
    · intro hh
      exact ⟨x,houter₀ hx,(hkeep hh).symm⟩
  have hp0 (b : AddCircle (4 * L)) :
      p (b,⟨0,by norm_num⟩) ∈ v '' (closure B₀.outer.inside \ B₀.outer.boundary ℝ) := by
    have hb : p (b,0) ∈ f₁ '' closure B₁.inner.inside :=
      image_mono hD₁.1 (hpzero.subset ⟨b,rfl⟩)
    have hc := hcapA.symm.subset hb
    obtain ⟨x,hx,hxp⟩ := hc.1
    refine ⟨x,⟨hx,?_⟩,hxp⟩
    intro hxr
    exact Set.disjoint_left.mp hrimA ⟨x,hxr,hxp⟩ hc.2
  obtain ⟨k,hk,hki,hkR,hkv,hkA,hkB⟩ := exists_original_finite_cap_push
    sphere hR he hSR hD₀ v hv hvi (fun x hx => hCS ⟨x,hx,rfl⟩)
    (hS₁.image_of_continuousOn hf₁.continuousOn).isClosed
    (hS₀.image_of_continuousOn hf₀.continuousOn).isClosed hZ hrimA hcupZ hvB
    p hp hp0 hproper hcover
  exact ⟨k,hk,hki,hkR,fun x hx => (hkv hx).trans (hkeep hx),hkA,hkB⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
