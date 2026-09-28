import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawEllipticity
import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology Matrix.Norms.Elementwise SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem smooth_det {G : V → Matrix (Fin n) (Fin n) ℝ}
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (fun x => (G x).det) := by
  have h : ContDiff ℝ ∞ (fun x =>
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, G x (σ i) i) := by
    apply ContDiff.sum
    intro σ _
    apply contDiff_const.mul
    apply contDiff_prod
    intro i _
    exact contDiff_pi.mp (contDiff_pi.mp hG (σ i)) i
  convert h using 1
  funext x
  exact Matrix.det_apply' (G x)


theorem raw_inverseGram_entry_contDiff (g : RiemannianMetric n V) (i j : Fin n) :
    ContDiff ℝ ∞ (fun x => (rawCoordinateGram g x)⁻¹ i j) := by
  have hG := rawCoordinateGram_contDiff g
  have hdet := smooth_det hG
  have hrow : ContDiff ℝ ∞ (fun x =>
      (rawCoordinateGram g x).updateRow j (Pi.single i 1)) := by
    apply contDiff_pi.mpr
    intro r
    apply contDiff_pi.mpr
    intro c
    by_cases hr : r = j
    · subst r
      simp only [Matrix.updateRow_apply, if_true]
      exact contDiff_const
    · simp only [Matrix.updateRow_apply, hr, if_false]
      exact contDiff_pi.mp (contDiff_pi.mp hG r) c
  have ha : ContDiff ℝ ∞ (fun x => (rawCoordinateGram g x).adjugate i j) := by
    simpa only [Matrix.adjugate_apply] using smooth_det hrow
  have hn (x : V) : (rawCoordinateGram g x).det ≠ 0 :=
    (rawCoordinateGram_posDef g x).det_pos.ne'
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul,
    Pi.inv_apply] using!
    (hdet.inv hn).mul ha




theorem exists_raw_principal_schwartz_coefficients (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) :
    ∃ A : Fin n → Fin n → 𝓢(V, ℝ), ∃ ell : ℝ, 0 < ell ∧
      (∀ i j x, A i j x = A j i x) ∧
      (∀ i j x, x ∈ K → A i j x = (rawCoordinateGram g x)⁻¹ i j) ∧
      ∀ x ∈ K, ∀ ξ : Fin n → ℝ,
        ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_le
  let bump : ContDiffBump (0 : V) :=
    ⟨R, R + 1, hR, by linarith⟩
  let η : 𝓢(V, ℝ) := bump.hasCompactSupport.toSchwartzMap bump.contDiff
  have hη : HasCompactSupport η := bump.hasCompactSupport
  have hηone (x : V) (hx : x ∈ K) : η x = 1 := by
    apply bump.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb x hx
  let A : Fin n → Fin n → 𝓢(V, ℝ) := fun i j =>
    EuclideanDerivativeNative.cutoffSchwartz η hη isOpen_univ (subset_univ _)
      (fun x => (rawCoordinateGram g x)⁻¹ i j)
      (raw_inverseGram_entry_contDiff g i j).contDiffOn
  have hA (i j : Fin n) (x : V) :
      A i j x = η x * (rawCoordinateGram g x)⁻¹ i j := rfl
  have hAK (i j : Fin n) (x : V) (hx : x ∈ K) :
      A i j x = (rawCoordinateGram g x)⁻¹ i j := by rw [hA, hηone x hx, one_mul]
  obtain ⟨c, hc, hlow⟩ := DeTurckNative.exists_uniform_inverse_quadratic_lower_bound
    (rawCoordinateGram g) hK (rawCoordinateGram_contDiff g).continuous.continuousOn
    (fun x _ => rawCoordinateGram_posDef g x)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨A, c / ((n : ℝ) + 1), div_pos hc hn, ?_, hAK, ?_⟩
  · intro i j x
    rw [hA, hA]
    congr 1
    exact (Matrix.isHermitian_iff_isSymm.mp
      (rawCoordinateGram_posDef g x).inv.isHermitian).apply j i
  · intro x hx ξ
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
      _ ≤ DeTurckNative.quadratic (rawCoordinateGram g x)⁻¹ ξ := hlow x hx ξ
      _ = ∑ i, ∑ j, A i j x * ξ i * ξ j := by simp only [DeTurckNative.quadratic, hAK _ _ x hx]

end PoincareConjecture.M35.Uniqueness.Heat
