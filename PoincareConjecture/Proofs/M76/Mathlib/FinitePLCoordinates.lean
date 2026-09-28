import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E}

theorem FinitePiecewiseAffineOn.postcomp (hf : FinitePiecewiseAffineOn f s)
    (a : F →ᴬ[ℝ] G) : FinitePiecewiseAffineOn (a ∘ f) s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨K, hK, rfl, hfaces.postcomp a⟩

theorem FinitePiecewiseAffineOn.precomp_affineEquiv [FiniteDimensional ℝ E]
    (hf : FinitePiecewiseAffineOn f s) (a : G ≃ᴬ[ℝ] E) :
    FinitePiecewiseAffineOn (f ∘ a) (a.symm '' s) := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  have hA := K.affineOnFaces_affine a.symm.toContinuousAffineMap
  let L := hA.embeddedImage a.symm.injective.injOn
  have hL : L.space = a.symm '' K.space := hA.embeddedImage_space _
  have ha : FinitePiecewiseAffineOn a (a.symm '' K.space) :=
    ⟨L, hA.embeddedImage_finite _ hK, hL, L.affineOnFaces_affine a.toContinuousAffineMap⟩
  exact hfaces.finitePiecewiseAffineOn hK |>.comp ha (by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx)

end Geometry

namespace Homeomorph

theorem IsFinitePL.affine_conjugate {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {s : Set E} {t : Set F} {e : s ≃ₜ t} (he : e.IsFinitePL)
    (a : E ≃ᴬ[ℝ] E') (b : F ≃ᴬ[ℝ] F') :
    ((a.toHomeomorph.image s).symm.trans (e.trans (b.toHomeomorph.image t))).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  refine ⟨b ∘ (f ∘ a.symm), (hf.precomp_affineEquiv a.symm).postcomp b.toContinuousAffineMap, ?_⟩
  intro x
  change b (e ((a.toHomeomorph.image s).symm x)) = b (f (a.symm x))
  rw [he]
  rfl

end Homeomorph
