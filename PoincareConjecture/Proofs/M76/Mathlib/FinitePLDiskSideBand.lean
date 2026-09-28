import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Geometry

namespace Set

local notation "I" => Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_disk_side_band_map
    {B q : Set E} (hB : IsFinitePLBallPair (ℝ × ℝ) B q)
    (F : E × ℝ → E) (hF : FinitePiecewiseAffineOn F (q ×ˢ I))
    (hi : InjOn F (q ×ˢ I)) (hzero : ∀ x ∈ q, F (x, 0) = x)
    (hcontact : ∀ x ∈ q ×ˢ I, F x ∈ B ↔ x.2 = 0) :
    ∃ H : (((B ×ˢ {(0 : ℝ)}) ∪ (q ×ˢ I)) : Set (E × ℝ)) ≃ₜ
        (B ∪ F '' (q ×ˢ I) : Set E), H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ B),
        (H ⟨(x, 0), Or.inl ⟨hx, rfl⟩⟩ : E) = x) ∧
      (∀ (x : E × ℝ) (hx : x ∈ q ×ˢ I),
        (H ⟨x, Or.inr hx⟩ : E) = F x) ∧
      ∀ x : ((B ×ˢ {(0 : ℝ)}) ∪ (q ×ˢ I) : Set (E × ℝ)),
        (x : E × ℝ) ∈ q ×ˢ {1} ↔ (H x : E) ∈ F '' (q ×ˢ {1}) := by
  classical
  let base : Set (E × ℝ) := B ×ˢ {(0 : ℝ)}
  let side : Set (E × ℝ) := q ×ˢ I
  let rim : Set (E × ℝ) := q ×ˢ {(1 : ℝ)}
  let f : E × ℝ → E := fun x => if x.2 = 0 then x.1 else F x
  have hfbase (x : E × ℝ) (hx : x ∈ base) : f x = x.1 := if_pos hx.2
  have hfside (x : E × ℝ) (hx : x ∈ side) : f x = F x := by
    by_cases ht : x.2 = 0
    · change (if x.2 = 0 then x.1 else F x) = F x
      rw [if_pos ht]
      have he : x = (x.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [he, hzero x.1 hx.1]
    · exact if_neg ht
  have hbaseball := hB.prod_singleton (0 : ℝ)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKb, _⟩, _⟩, _⟩ := hbaseball
  have hfbasePL : FinitePiecewiseAffineOn f base := by
    have hfst : FinitePiecewiseAffineOn (Prod.fst : E × ℝ → E) base :=
      ⟨K, hK, hKb, K.affineOnFaces_affine
        (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
    exact hfst.congr (fun x hx => (hfbase x hx).symm)
  have hfsidePL : FinitePiecewiseAffineOn f side :=
    hF.congr (fun x hx => (hfside x hx).symm)
  have hf : FinitePiecewiseAffineOn f (base ∪ side) :=
    finitePiecewiseAffineOn_union hfbasePL hfsidePL
  have hcross (x y : E × ℝ) (hx : x ∈ base) (hy : y ∈ side)
      (he : f x = f y) : x = y := by
    have hyB : F y ∈ B := by rw [← hfside y hy, ← he, hfbase x hx]; exact hx.1
    have hyt : y.2 = 0 := (hcontact y hy).mp hyB
    have hFval : F y = y.1 := by
      have he' : y = (y.1, (0 : ℝ)) := Prod.ext rfl hyt
      rw [he', hzero y.1 hy.1]
    exact Prod.ext ((hfbase x hx).symm.trans (he.trans ((hfside y hy).trans hFval)))
      (hx.2.trans hyt.symm)
  have hfi : InjOn f (base ∪ side) := by
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Prod.ext ((hfbase x hx).symm.trans (he.trans (hfbase y hy)))
        (hx.2.trans hy.2.symm)
    · exact hcross x y hx hy he
    · exact (hcross y x hy hx he.symm).symm
    · exact hi hx hy ((hfside x hx).symm.trans (he.trans (hfside y hy)))
  have himage : f '' (base ∪ side) = B ∪ F '' side := by
    ext x
    constructor
    · rintro ⟨y, hy | hy, rfl⟩
      · rw [hfbase y hy]
        exact Or.inl hy.1
      · exact Or.inr ⟨y, hy, (hfside y hy).symm⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact ⟨(x, 0), Or.inl ⟨hx, rfl⟩, hfbase (x, 0) ⟨hx, rfl⟩⟩
      · exact ⟨y, Or.inr hy, hfside y hy⟩
  have hrimside : rim ⊆ side := by
    intro x hx
    exact ⟨hx.1, by rw [show x.2 = 1 from hx.2]; exact ⟨zero_le_one, le_rfl⟩⟩
  have hrimimage : f '' rim = F '' rim := image_congr (fun x hx => hfside x (hrimside hx))
  obtain ⟨H0, _, hH0val⟩ := hf.exists_homeomorph_image hfi
  let H := H0.trans (Homeomorph.setCongr himage)
  have hHval (x : (base ∪ side : Set (E × ℝ))) : (H x : E) = f x := hH0val x
  have hH : H.IsFinitePL := ⟨f, hf, hHval⟩
  refine ⟨H, hH, ?_, ?_, ?_⟩
  · intro x hx
    exact (hHval ⟨(x, 0), Or.inl ⟨hx, rfl⟩⟩).trans (hfbase (x, 0) ⟨hx, rfl⟩)
  · intro x hx
    exact (hHval ⟨x, Or.inr hx⟩).trans (hfside x hx)
  · intro x
    rw [hHval, ← hrimimage]
    constructor
    · exact mem_image_of_mem f
    · rintro ⟨y, hy, hyx⟩
      have he : y = (x : E × ℝ) := hfi (Or.inr (hrimside hy)) x.property hyx
      exact he ▸ hy

end Set
