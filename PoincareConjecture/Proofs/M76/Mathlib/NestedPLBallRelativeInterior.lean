import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.RelativeSetInteriors











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem IsFinitePLBallPair.interior_preimage_subball {a b d q : Set E}
    (hd : IsFinitePLBallPair F d q) (ha : IsFinitePLBallPair F a b)
    (had : a ⊆ d \ q) :
    interior ((Subtype.val : d → E) ⁻¹' a) = (Subtype.val : d → E) ⁻¹' (a \ b) := by
  obtain ⟨_, C, _, _, _, e, he, heb⟩ := hd
  obtain ⟨f, hf, hef⟩ := he
  have has : a ⊆ d := had.trans sdiff_subset
  have hfinj : InjOn f d := by
    intro x hx y hy hxy
    have h : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
      Subtype.ext ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.injective h)
  have hfa : IsFinitePLBallPair F (f '' a) (f '' b) :=
    ha.image_of_subset hf has hfinj
  have hinside : f '' a ⊆ interior C := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have hfront : (e ⟨x, has hx⟩ : F) ∈ frontier C := by
      refine ⟨subset_closure (e ⟨x, has hx⟩).property, ?_⟩
      rwa [hef]
    exact (had hx).2 ((heb ⟨x, has hx⟩).mpr hfront)
  have hpre (s : Set E) (hs : s ⊆ d) :
      (Subtype.val : d → E) ⁻¹' s =
        e ⁻¹' ((Subtype.val : C → F) ⁻¹' (f '' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, (hef x).symm⟩
    · rintro ⟨y, hy, hyx⟩
      have heq : y = (x : E) := hfinj (hs hy) x.property (hyx.trans (hef x))
      change (x : E) ∈ s
      exact heq ▸ hy
  calc
    interior ((Subtype.val : d → E) ⁻¹' a) =
        e ⁻¹' ((Subtype.val : C → F) ⁻¹' interior (f '' a)) := by
      rw [hpre a has, ← e.preimage_interior,
        interior_preimage_val_of_subset_interior hinside]
    _ = e ⁻¹' ((Subtype.val : C → F) ⁻¹' (f '' (a \ b))) := by
      rw [hfa.interior_eq_sdiff_of_finrank_eq rfl, (hfinj.mono has).image_sdiff_subset ha.1]
    _ = (Subtype.val : d → E) ⁻¹' (a \ b) :=
      (hpre (a \ b) (sdiff_subset.trans has)).symm

end Set
