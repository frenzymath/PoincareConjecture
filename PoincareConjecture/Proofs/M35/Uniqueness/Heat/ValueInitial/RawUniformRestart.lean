import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.UniformPrincipal
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactVectorHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_slab_cutoff_ellipticity {J I : Set ℝ} (F : RicciFlow n V J)
    (hI : IsCompact I) (hIJ : I ⊆ J) {K : Set V} (hK : IsCompact K)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ t ∈ I, ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤
        ∑ i, ∑ j, rawCutoffPrincipalCoefficient (F.metric t) η hη i j x * ξ i * ξ j := by
  obtain ⟨c, hc, hb⟩ := exists_raw_slab_ellipticity F hI hIJ hK
  have hn : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨c / ((n : ℝ) + 1), div_pos hc hn, ?_⟩
  intro t ht x hx ξ
  have hsum : (∑ i : Fin n, ξ i ^ 2) ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin n, ‖ξ‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_le_pi_norm ξ i
        rw [Real.norm_eq_abs] at h
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr h
      _ = (n : ℝ) * ‖ξ‖ ^ 2 := by simp
      _ ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  calc
    c / ((n : ℝ) + 1) * (∑ i, ξ i ^ 2) ≤
        c / ((n : ℝ) + 1) * (((n : ℝ) + 1) * ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hc.le hn.le)
    _ = c * ‖ξ‖ ^ 2 := by field_simp
    _ ≤ DeTurckNative.quadratic (rawCoordinateGram (F.metric t) x)⁻¹ ξ := hb t ht x hx ξ
    _ = _ := by
      simp only [DeTurckNative.quadratic, rawCutoffPrincipalCoefficient_apply, hηK x hx,
        one_mul]

theorem exists_raw_uniform_value_restart {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) (hηK : ∀ x ∈ K, η x = 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ r ∈ Icc a b, ∀ T ∈ Icc 0 τ, r + T ≤ b →
      ∀ u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K),
      ∃ (v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
        (U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)),
        PrincipalValueHeat K
          (fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη)
          (fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη) r T u₀ v U := by
  refine (exists_raw_slab_cutoff_ellipticity (I := Icc a b)
    F isCompact_Icc hJ hK η hη hηK).elim ?_
  intro ell he
  exact exists_uniform_principal_value_restart hK
    (fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη) he.1
    (fun r _ => rawCutoffPrincipalCoefficient_symmetric (F.metric r) η hη) he.2
    (continuousOn_raw_principalFormOperator F isCompact_Icc hJ K η hη hη1)
    (fun t => rawLowerFormOperator (F.connection t) hK.isClosed η hη)
    (continuousOn_rawLowerFormOperator F isCompact_Icc hJ hK.isClosed η hη hη1)

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
