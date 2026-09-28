import PoincareConjecture.Proofs.M76.Wall.Mathlib.TwoRayStraightening
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap

theorem exists_height_of_distinct_rays
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ, 0 < t → u ≠ t • v) :
    ∃ ell : E →L[ℝ] ℝ, ell u < 0 ∧ ell v = 1 := by
  obtain ⟨psi, hpsi⟩ := Module.Projective.exists_dual_eq_one ℝ hv
  let P : Submodule ℝ E := Submodule.span ℝ {v}
  have hvP : v ∈ P := Submodule.mem_span_singleton_self v
  by_cases huP : u ∈ P
  · obtain ⟨t, htu⟩ := Submodule.mem_span_singleton.mp huP
    have ht0 : t ≠ 0 := by
      intro ht
      exact hu (by simpa only [ht, zero_smul] using htu.symm)
    have ht : t < 0 := lt_of_le_of_ne
      (le_of_not_gt (fun ht => hne t ht htu.symm)) ht0
    refine ⟨psi.toContinuousLinearMap, ?_, hpsi⟩
    change psi u < 0
    rw [← htu, map_smul, hpsi, smul_eq_mul, mul_one]
    exact ht
  · obtain ⟨phi, hphi, hphiP⟩ :=
      Submodule.exists_dual_map_eq_bot_of_notMem huP inferInstance
    have hphiv : phi v = 0 := by
      have hm : phi v ∈ P.map phi := ⟨v, hvP, rfl⟩
      rw [hphiP] at hm
      exact hm
    let eta : E →ₗ[ℝ] ℝ := (phi u)⁻¹ • phi
    have hetau : eta u = 1 := by
      simp only [eta, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hphi]
    have hetav : eta v = 0 := by
      simp only [eta, LinearMap.smul_apply, hphiv, smul_zero]
    let ell : E →ₗ[ℝ] ℝ := psi - (psi u + 1) • eta
    refine ⟨ell.toContinuousLinearMap, ?_, ?_⟩
    · change ell u < 0
      simp only [ell, LinearMap.sub_apply, LinearMap.smul_apply, hetau,
        smul_eq_mul, mul_one]
      linarith
    · change ell v = 1
      simp only [ell, LinearMap.sub_apply, LinearMap.smul_apply, hetav,
        smul_zero, sub_zero, hpsi]

theorem exists_straightening_of_distinct_rays
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hne : ∀ t : ℝ, 0 < t → u ≠ t • v) :
    ∃ (ell : E →L[ℝ] ℝ) (w : E), ell u < 0 ∧ ell v = 1 ∧ ell w = 1 ∧
      ∃ H : E ≃ₜ E, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
        H 0 = 0 ∧ (∀ x, ell (H x) = ell x) ∧
        (∀ t : ℝ, 0 ≤ t → H (t • u) = (t * ell u) • w) ∧
        ∀ t : ℝ, 0 ≤ t → H (t • v) = t • w := by
  obtain ⟨ell, hellu, hellv⟩ := exists_height_of_distinct_rays hu hv hne
  obtain ⟨w, hw, H, hPL, hzero, hheight, hnegative, hpositive⟩ :=
    ell.exists_two_ray_straightening u v hellu (by rw [hellv]; exact zero_lt_one)
  refine ⟨ell, w, hellu, hellv, hw, H, hPL, hzero, hheight, hnegative, ?_⟩
  intro t ht
  simpa only [hellv, mul_one] using hpositive t ht

end ContinuousLinearMap
