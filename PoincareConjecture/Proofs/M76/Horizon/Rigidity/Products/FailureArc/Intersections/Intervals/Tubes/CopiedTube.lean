import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Tubes.OriginalStrip

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_copied_selected_interval_tube
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T Q₀ Q₁ C D : Set P2} {f₀ f₁ f : P2 → X}
    (he : PLDomain e R) (a : P2 ≃ᴬ[ℝ] P2)
    (hS : IsCompact S) (hT : IsCompact T) (hdis : Disjoint S (a '' T))
    (hf₀ : ContinuousOn f₀ S) (hf₁ : ContinuousOn f₁ T)
    (hfi : InjOn f₀ S) (hgi : InjOn f₁ T)
    (hf : PolyhedralPLInCharts e f (S ∪ a '' T))
    (hkeep₀ : EqOn f f₀ S) (hkeep₁ : ∀ x ∈ T, f (a x) = f₁ x)
    (hQ₁ : Q₁ ⊆ T) (hC : C ⊆ S) (hD : D ⊆ T)
    (hball : IsFinitePLBallPair ℝ C (C ∩ Q₀)) (himage : f₀ '' C = f₁ '' D)
    (hrest : IsClosed ((S ∩ f₀ ⁻¹' (f₁ '' T)) \ C))
    (hdouble : doubleLocusOn f (S ∪ a '' T) =
      (S ∩ f₀ ⁻¹' (f₁ '' T)) ∪ a '' (T ∩ f₁ ⁻¹' (f₀ '' S)))
    (old : SourceDoubleComponents e f (S ∪ a '' T) (Q₀ ∪ a '' Q₁) R)
    (hin : MapsTo f (S ∪ a '' T) R)
    (hfront : ∀ x ∈ S ∪ a '' T, f x ∈ frontier R ↔ x ∈ Q₀ ∪ a '' Q₁)
    (hW : IsOpen W) (hCW : f₀ '' C ⊆ W) :
    ∃ (c : Bool → P2 → P2) (τ : C3 → X),
      (∀ j, FinitePiecewiseAffineOn (c j) source ∧
        IsEmbedding (fun p : source => c j p)) ∧
      MapsTo (c false) source S ∧ MapsTo (c true) source (a '' T) ∧
      PolyhedralPLInCharts e τ tube ∧ IsEmbedding (fun z : tube => τ z) ∧
      MapsTo τ tube R ∧ MapsTo τ tube W ∧
      (∀ j p, p ∈ source → f (c j p) = τ (originalStripSheet j p)) ∧
      (S ∪ a '' T) ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source ∧
      c false '' arm 0 = C ∧ c true '' arm 0 = a '' D ∧
      ∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
  have hCdouble : C ⊆ doubleLocusOn f (S ∪ a '' T) := by
    intro x hx
    rw [hdouble]
    exact Or.inl ⟨hC hx,image_mono hD (himage.subset ⟨x,hx,rfl⟩)⟩
  have hclosedB : IsClosed (T ∩ f₁ ⁻¹' (f₀ '' S)) :=
    hf₁.preimage_isClosed_of_isClosed hT.isClosed (hS.image_of_continuousOn hf₀).isClosed
  have hrest' := copied_pair_selected_complement_closed a hdis hC
    (inter_subset_left (s := T)) hdouble hrest hclosedB
  have hCQ : C ∩ (Q₀ ∪ a '' Q₁) = C ∩ Q₀ := by
    ext x
    constructor
    · rintro ⟨hx,hq | ⟨y,hy,hyx⟩⟩
      · exact ⟨hx,hq⟩
      · exact (disjoint_left.mp hdis (hC hx) ⟨y,hQ₁ hy,hyx⟩).elim
    · exact fun h => ⟨h.1,Or.inl h.2⟩
  have hfirst : f '' C = f₀ '' C := image_congr (hkeep₀.mono hC)
  have hiC : InjOn f C := by
    intro x hx y hy hxy
    exact hfi (hC hx) (hC hy) ((hkeep₀ (hC hx)).symm.trans (hxy.trans (hkeep₀ (hC hy))))
  obtain ⟨c,τ,hc,_,hτ,hτi,hτR,hτW,hval,hpre,hcenter,hτfront,_⟩ :=
    old.exists_selected_interval_tube hf he (hCQ.symm ▸ hball) hCdouble hrest' hiC
      (fun _ hx => Or.inr (image_mono hD hx)) (hdis.mono hC (image_mono hD))
      (copied_pair_selected_fibers a hC hD hfi hgi hkeep₀ hkeep₁ himage)
      hin hfront hW (hfirst.symm ▸ hCW)
  have hcenter₀ : c false '' arm 0 = C := by simpa using hcenter false
  have hcenter₁ : c true '' arm 0 = a '' D := by simpa using hcenter true
  have hzero : ((0,0) : P2) ∈ arm 0 := by
    exact ⟨⟨by norm_num,by norm_num⟩,rfl⟩
  obtain ⟨hc₀,hc₁⟩ := interval_strips_stay_in_marked_copies hS.isClosed
    (a.toHomeomorph.isClosedMap _ hT.isClosed) hdis c
    (fun j => (hc j).1.continuousOn) (fun j => (hc j).2.2)
    (hC (hcenter₀.subset ⟨(0,0),hzero,rfl⟩))
    (image_mono hD (hcenter₁.subset ⟨(0,0),hzero,rfl⟩))
  exact ⟨c,τ,fun j => ⟨(hc j).1,(hc j).2.1⟩,hc₀,hc₁,
    hτ,hτi,hτR,hτW,hval,hpre,hcenter₀,hcenter₁,hτfront⟩

end PoincareConjecture.M76.Dehn.Annuli
