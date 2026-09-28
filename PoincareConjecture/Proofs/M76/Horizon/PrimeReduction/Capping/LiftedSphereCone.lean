import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierConeBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeAffine









set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem IsFinitePL.isFinitePLBallPair_lifted_sphere_cone
    {S : Set E} {T : Set F} {e : S ≃ₜ frontier T} (he : e.IsFinitePL)
    (hne : S.Nonempty) (hT : IsCompact T) (hcv : Convex ℝ T)
    (hTi : (interior T).Nonempty) :
    IsFinitePLBallPair F
      (convexJoin ℝ {((0 : E), (1 : ℝ))} ((fun x : E => (x, (0 : ℝ))) '' S))
      ((fun x : E => (x, (0 : ℝ))) '' S) := by
  classical
  let u : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 1)
  have hui : Function.Injective u := fun x y h => congrArg Prod.fst h
  have huPL : FinitePiecewiseAffineOn u S := by
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he
    exact ⟨K, hK, hKs, K.affineOnFaces_affine u⟩
  obtain ⟨U, hU, _⟩ := huPL.exists_homeomorph_image hui.injOn
  have he' := hU.symm.trans he
  let C : Set (E × ℝ) := Prod.snd ⁻¹' Iic (1 : ℝ)
  have hCcv : Convex ℝ C :=
    (convex_Iic (1 : ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ)
  have hC0 : (0 : E × ℝ) ∈ interior C := by
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset
      ((isOpen_lt continuous_snd continuous_const).mem_nhds (by norm_num))
      (fun x hx => le_of_lt hx)
  have hSC : u '' S ⊆ frontier C := by
    have hfront := (ContinuousLinearMap.snd ℝ E ℝ).frontier_preimage
      (fun y => ⟨(0, y), rfl⟩) (Iic (1 : ℝ))
    rw [frontier_Iic] at hfront
    intro x hx
    rw [show C = (ContinuousLinearMap.snd ℝ E ℝ) ⁻¹' Iic (1 : ℝ) from rfl,
      hfront]
    rcases hx with ⟨y, hy, rfl⟩
    rfl
  have hcap := he'.isFinitePLBallPair_radial_cone hCcv hC0 hSC
    (hne.image u) hT hcv hTi
  let a : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ (E × ℝ) 1 -
        (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hai : Function.Injective a := by
    intro x y h
    apply Prod.ext
    · simpa [a] using congrArg Prod.fst h
    · have hz := congrArg Prod.snd h
      change 1 - x.2 = 1 - y.2 at hz
      linarith
  have habase : a '' (u '' S) = (fun x : E => (x, (0 : ℝ))) '' S := by
    rw [image_image]
    apply image_congr
    intro x hx
    simp [a, u]
  have hcone : a '' convexJoin ℝ {0} (u '' S) =
      convexJoin ℝ {((0 : E), (1 : ℝ))} ((fun x : E => (x, (0 : ℝ))) '' S) := by
    change (a : E × ℝ →ᵃ[ℝ] E × ℝ) '' _ = _
    rw [AffineMap.image_convexJoin, image_singleton]
    change convexJoin ℝ {a 0} (a '' (u '' S)) = _
    rw [habase]
    simp [a]
  have h := hcap.affine_image a hai.injOn
  rwa [hcone, habase] at h

end Homeomorph
