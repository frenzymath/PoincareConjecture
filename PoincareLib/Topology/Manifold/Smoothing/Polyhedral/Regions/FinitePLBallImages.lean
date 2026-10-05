import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallPairs

/-!
# Embedded images of finite PL ball pairs

An injective finite piecewise-affine map transports a ball pair to
its exact image, including its specified boundary. This applies to
the affine slice inclusion in Alexander 1924, p. 7. See Hudson 1969,
pp. 15--19 and M76 derivation 123.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An injective finite PL map gives a finite PL homeomorphism
onto its exact image. See Hudson pp. 15--19 and derivation 123. -/
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

/-- Finite PL embeddings transport ball pairs with the exact image
boundary. The model dimension is unchanged. See Alexander p. 7,
Hudson pp. 15--19 and M76 derivation 123. -/
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

/-- Restrict a finite PL embedding of a larger carrier to an
existing ball pair before transporting that pair. Its triangulation
is supplied by the ball model. See M76 derivation 142. -/
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

/-- An injective continuous affine map transports a finite PL
ball pair to a finite PL ball pair. See Alexander p. 7 and
M76 derivation 123. -/
theorem IsFinitePLBallPair.affine_image {s b : Set X}
    (hs : IsFinitePLBallPair E s b) (a : X →ᴬ[ℝ] Y) (ha : InjOn a s) :
    IsFinitePLBallPair E (a '' s) (a '' b) := by
  have hcopy := hs
  obtain ⟨_, _, _, _, _, e, ⟨f, ⟨K, hK, hspace, _⟩, _⟩, _⟩ := hcopy
  exact hs.image ⟨K, hK, hspace, K.affineOnFaces_affine a⟩ ha

end Set
