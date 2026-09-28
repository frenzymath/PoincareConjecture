import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem FinitePiecewiseAffineOn.exists_homeomorph_image {f : E → F} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) (hinj : InjOn f s) :
    ∃ e : s ≃ₜ f '' s, e.IsFinitePL ∧ ∀ x : s, (e x : F) = f x := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨hfaces.homeomorphImage hK hinj,
    ⟨f, hfaces.finitePiecewiseAffineOn hK, fun _ => rfl⟩, fun _ => rfl⟩

end Geometry

namespace Set

variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]




theorem IsFinitePLBallPair.image {s b : Set X} (hs : IsFinitePLBallPair E s b)
    {f : X → Y} (hf : FinitePiecewiseAffineOn f s) (hinj : InjOn f s) :
    IsFinitePLBallPair E (f '' s) (f '' b) := by
  obtain ⟨e, he, heval⟩ := hf.exists_homeomorph_image hinj
  apply hs.of_homeomorph (image_mono hs.1) e.symm he.symm
  intro y
  have hy : f (e.symm y) = (y : Y) := by
    rw [← heval, e.apply_symm_apply]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxe : x = (e.symm y : X) := hinj (hs.1 hx) (e.symm y).property (hxy.trans hy.symm)
    rwa [← hxe]
  · intro hx
    exact ⟨e.symm y, hx, hy⟩




theorem IsFinitePLBallPair.image_of_subset {s b t : Set X}
    (hs : IsFinitePLBallPair E s b) {f : X → Y}
    (hf : FinitePiecewiseAffineOn f t) (hst : s ⊆ t) (hinj : InjOn f t) :
    IsFinitePLBallPair E (f '' s) (f '' b) := by
  have hcopy := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hfs : FinitePiecewiseAffineOn f s := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hst)
  exact hs.image hfs (hinj.mono hst)




theorem IsFinitePLBallPair.affine_image {s b : Set X}
    (hs : IsFinitePLBallPair E s b) (a : X →ᴬ[ℝ] Y) (ha : InjOn a s) :
    IsFinitePLBallPair E (a '' s) (a '' b) := by
  have hcopy := hs
  obtain ⟨_, _, _, _, _, e, ⟨f, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  exact hs.image ⟨K, hK, hspace, K.affineOnFaces_affine a⟩ ha

end Set
