import PoincareConjecture.Proofs.M25.Topology3D.Plane.GenericProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

open Function

namespace PoincareConjecture.M25.Topology3D

theorem exists_linearMap_prod_bijective {K : Type*} [Field K]
    (H : (K × K) →ₗ[K] K) (hH : H ≠ 0) :
    ∃ X : (K × K) →ₗ[K] K, Bijective (X.prod H) := by
  have hformula (z : K × K) : H z = z.1 * H (1, 0) + z.2 * H (0, 1) := by
    calc
      H z = H (z.1 • (1, 0) + z.2 • (0, 1)) := by congr 1; ext <;> simp
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  by_cases hB : H (0, 1) = 0
  · have hA : H (1, 0) ≠ 0 := by
      intro hA
      apply hH
      apply LinearMap.ext
      intro z
      simp only [hformula z, hA, hB, mul_zero, add_zero, LinearMap.zero_apply]
    have hinj : Injective ((LinearMap.snd K K K).prod H) := by
      intro a b hab
      have hy : a.2 = b.2 := congrArg Prod.fst hab
      have hh : H a = H b := congrArg Prod.snd hab
      rw [hformula a, hformula b, hB, mul_zero, mul_zero, add_zero, add_zero] at hh
      exact Prod.ext (mul_right_cancel₀ hA hh) hy
    exact ⟨LinearMap.snd K K K, hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  · have hinj : Injective ((LinearMap.fst K K K).prod H) := by
      intro a b hab
      have hx := congrArg Prod.fst hab
      change a.1 = b.1 at hx
      have hh : H a = H b := congrArg Prod.snd hab
      rw [hformula a, hformula b, hx] at hh
      exact Prod.ext hx (mul_right_cancel₀ hB (add_left_cancel hh))
    exact ⟨LinearMap.fst K K K, hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem exists_linearEquiv_snd_eq {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (hdim : Module.finrank K E = 2)
    (H : E →ₗ[K] K) (hH : H ≠ 0) :
    ∃ e : E ≃ₗ[K] (K × K), ∀ x, (e x).2 = H x := by
  let e0 : E ≃ₗ[K] (K × K) := LinearEquiv.ofFinrankEq E (K × K) (by simp [hdim])
  let H0 : (K × K) →ₗ[K] K := H.comp e0.symm.toLinearMap
  have hH0 : H0 ≠ 0 := by
    intro hz
    apply hH
    ext x
    have hx := LinearMap.congr_fun hz (e0 x)
    simpa only [H0, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.zero_apply] using hx
  obtain ⟨X, hX⟩ := exists_linearMap_prod_bijective H0 hH0
  refine ⟨e0.trans (LinearEquiv.ofBijective (X.prod H0) hX), ?_⟩
  intro x
  change H (e0.symm (e0 x)) = H x
  rw [e0.symm_apply_apply]

theorem exists_continuousLinearEquiv_snd_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (H : E →ₗ[ℝ] ℝ) (hH : H ≠ 0) :
    ∃ e : E ≃L[ℝ] (ℝ × ℝ), ∀ x, (e x).2 = H x := by
  obtain ⟨e, he⟩ := exists_linearEquiv_snd_eq hdim H hH
  exact ⟨e.toContinuousLinearEquiv, he⟩

theorem exists_continuousLinearEquiv_snd_injective_comp_finite {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite I]
    (hdim : Module.finrank ℝ E = 2) (v : I → E) (hv : Injective v) :
    ∃ e : E ≃L[ℝ] (ℝ × ℝ), Injective (fun i => (e (v i)).2) := by
  rcases subsingleton_or_nontrivial I with hI | hI
  · refine ⟨(LinearEquiv.ofFinrankEq E (ℝ × ℝ) (by simp [hdim])).toContinuousLinearEquiv,
      fun i j _ => Subsingleton.elim i j⟩
  · obtain ⟨H, hH⟩ := exists_linearMap_injective_comp_finite (K := ℝ) v hv
    have hne : H ≠ 0 := by
      intro hz
      obtain ⟨i, j, hij⟩ := exists_pair_ne I
      exact hij (hH (by simp [hz]))
    obtain ⟨e, he⟩ := exists_continuousLinearEquiv_snd_eq hdim H hne
    refine ⟨e, fun i j hij => hH ?_⟩
    simpa only [Function.comp_apply, he] using hij

end PoincareConjecture.M25.Topology3D
