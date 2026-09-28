import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.Exteriors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.SpanningDiskComplement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

def spanningStripEnd (t : ℝ) : Set P2 := {t} ×ˢ Icc (-1 : ℝ) 1

theorem spanningStripEnd_ball (t : ℝ) :
    IsFinitePLBallPair ℝ (spanningStripEnd t) {(t,-1),(t,1)} := by
  let a : ℝ →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.const ℝ ℝ t).prod (ContinuousAffineMap.id ℝ ℝ)
  have ha : InjOn a (Icc (-1 : ℝ) 1) := fun x _ y _ h => congrArg Prod.snd h
  have hs : a '' Icc (-1 : ℝ) 1 = spanningStripEnd t := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨rfl,hy⟩
    · rintro ⟨hx,hy⟩
      exact ⟨x.2,hy,Prod.ext hx.symm rfl⟩
  have hb : a '' ({-1,1} : Set ℝ) = {(t,-1),(t,1)} := by
    rw [image_pair]
    rfl
  exact hs ▸ hb ▸ (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).affine_image a ha

theorem spanningStripEnd_subset_source {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    spanningStripEnd t ⊆ source := by
  rintro p ⟨hp,hq⟩
  exact ⟨(hp : p.1 = t) ▸ ht,hq⟩

theorem spanningStripSource_ball : IsFinitePLBallPair P2 source (frontier source) := by
  have h := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  exact h.frontier_eq_of_finrank_eq rfl ▸ h

theorem spanningStripSource_frontier (p : P2) :
    p ∈ frontier source ↔ p ∈ source ∧
      (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = -1 ∨ p.2 = 1) := by
  have h := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  rw [source,h.frontier_eq_of_finrank_eq rfl]
  simp only [mem_union,mem_prod,mem_insert_iff,mem_singleton_iff,mem_Icc]
  constructor
  · rintro (⟨h|h,hp⟩ | ⟨hp,h|h⟩)
    · exact ⟨⟨by rw [h]; norm_num,hp⟩,Or.inl h⟩
    · exact ⟨⟨by rw [h]; norm_num,hp⟩,Or.inr (Or.inl h)⟩
    · exact ⟨⟨hp,by rw [h]; norm_num⟩,Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨⟨hp,by rw [h]; norm_num⟩,Or.inr (Or.inr (Or.inr h))⟩
  · rintro ⟨⟨hp,hq⟩,h|h|h|h⟩
    · exact Or.inl ⟨Or.inl h,hq⟩
    · exact Or.inl ⟨Or.inr h,hq⟩
    · exact Or.inr ⟨hp,Or.inl h⟩
    · exact Or.inr ⟨hp,Or.inr h⟩

theorem spanningStripEnd_subset_frontier {t : ℝ} (ht : t = 0 ∨ t = 1) :
    spanningStripEnd t ⊆ frontier source := by
  intro p hp
  apply (spanningStripSource_frontier p).mpr
  refine ⟨spanningStripEnd_subset_source (by rcases ht with rfl|rfl <;> norm_num) hp,?_⟩
  rcases ht with h|h
  · exact Or.inl (hp.1.trans h)
  · exact Or.inr (Or.inl (hp.1.trans h))

end PoincareConjecture.M76.Dehn.Annuli
