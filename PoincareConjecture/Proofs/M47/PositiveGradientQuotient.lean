import PoincareConjecture.Proofs.M47.PositiveGradientEvolution

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M47Positive

private theorem hessian_quotient_remainder_nonpos {R G H K : ℝ}
    (hR : 0 < R) (hH : 0 ≤ H) (hK : K ≤ Real.sqrt H * G) :
    -2 * H / R + 4 * K / R ^ 2 - 2 * G ^ 2 / R ^ 3 ≤ 0 := by
  have hsquare := sq_nonneg (Real.sqrt H * R - G)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hH] at hsquare
  have hKR := mul_le_mul_of_nonneg_right hK hR.le
  have hcore : -2 * H * R ^ 2 + 4 * K * R - 2 * G ^ 2 ≤ 0 := by
    nlinarith only [hsquare, hKR]
  apply nonpos_of_mul_nonpos_left (b := R ^ 3) ?_ (pow_pos hR 3)
  have hid : (-2 * H / R + 4 * K / R ^ 2 - 2 * G ^ 2 / R ^ 3) * R ^ 3 =
      -2 * H * R ^ 2 + 4 * K * R - 2 * G ^ 2 := by
    field_simp [hR.ne']
  rw [hid]
  exact hcore

private theorem quotient_parabolic_bound {R G S H K V Lr Lg Lq W dq : ℝ}
    (hR : 0 < R) (hH : 0 ≤ H) (hK : K ≤ Real.sqrt H * G)
    (hgradient : 2 * K = G / R * G + R * W)
    (hspace : Lg = G / R * Lr + R * Lq + 2 * W)
    (htime : dq * R + G / R * (Lr + 2 * S) = Lg - 2 * H + 4 * V) :
    dq ≤ Lq + 4 / R * V - 2 * S * G / R ^ 2 := by
  have hrem := hessian_quotient_remainder_nonpos hR hH hK
  have hid : dq - (Lq + 4 / R * V - 2 * S * G / R ^ 2) =
      -2 * H / R + 4 * K / R ^ 2 - 2 * G ^ 2 / R ^ 3 := by
    field_simp [hR.ne'] at htime hspace hgradient ⊢
    linear_combination R * htime + R * hspace - 2 * hgradient
  linarith only [hid, hrem]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem scalar_gradient_quotient_evolution_le
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    (hR : ∀ y, 0 < (F.connection t).scalarCurvature y) (x : M) :
    deriv (fun s => (F.metric s).inner x
        ((F.connection s).gradient (F.connection s).scalarCurvature x)
        ((F.connection s).gradient (F.connection s).scalarCurvature x) /
          (F.connection s).scalarCurvature x) t ≤
      (F.connection t).laplacian (fun y => (F.metric t).inner y
        ((F.connection t).gradient (F.connection t).scalarCurvature y)
        ((F.connection t).gradient (F.connection t).scalarCurvature y) /
          (F.connection t).scalarCurvature y) x +
        4 / (F.connection t).scalarCurvature x * (F.metric t).inner x
          ((F.connection t).gradient (F.connection t).scalarCurvature x)
          ((F.connection t).gradient (F.connection t).ricciNormSq x) -
        2 * (F.connection t).ricciNormSq x * (F.metric t).inner x
          ((F.connection t).gradient (F.connection t).scalarCurvature x)
          ((F.connection t).gradient (F.connection t).scalarCurvature x) /
            (F.connection t).scalarCurvature x ^ 2 := by
  let D := F.connection t
  let R := D.scalarCurvature
  let S := D.ricciNormSq
  let G := fun y => (F.metric t).inner y (D.gradient R y) (D.gradient R y)
  let q := fun y => G y / R y
  let H := ∑ i, ∑ j, (D.hessian R x
    ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x j)) ^ 2
  let K := D.hessian R x (D.gradient R x) (D.gradient R x)
  let V := (F.metric t).inner x (D.gradient R x) (D.gradient S x)
  let W := (F.metric t).inner x (D.gradient q x) (D.gradient R x)
  let dq := deriv (fun s => (F.metric s).inner x
    ((F.connection s).gradient (F.connection s).scalarCurvature x)
    ((F.connection s).gradient (F.connection s).scalarCurvature x) /
      (F.connection s).scalarCurvature x) t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hRs := hD.contMDiff_scalarCurvature
  have hGs := contMDiff_gradient_energy D hRs
  have hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q :=
    hGs.div₀ hRs (fun y => (hR y).ne')
  have hprod : (fun y => q y * R y) = G := by
    funext y
    exact div_mul_cancel₀ _ (hR y).ne'
  have hgradient : 2 * K = G x / R x * G x + R x * W := by
    have hg := D.gradient_mul ((hqs x).mdifferentiableAt (by simp))
      ((hRs x).mdifferentiableAt (by simp))
    change D.gradient (fun y => q y * R y) x =
      q x • D.gradient R x + R x • D.gradient q x at hg
    rw [hprod] at hg
    have hinner := congrArg (fun v => (F.metric t).inner x v (D.gradient R x)) hg
    rw [gradient_energy_pairing D hRs x] at hinner
    simpa only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul] using hinner
  have hspace : D.laplacian G x = G x / R x * D.laplacian R x +
      R x * D.laplacian q x + 2 * W := by
    have h := D.laplacian_mul hqs hRs x
    change D.laplacian (fun y => q y * R y) x = _ at h
    rw [hprod] at h
    exact h
  have hdR := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hdG := hasDerivAt_scalar_gradient_energy hC F ht x
  have hdq := hdG.div hdR (hR x).ne'
  have hRx : 0 < R x := hR x
  have htime : dq * R x + G x / R x * (D.laplacian R x + 2 * S x) =
      D.laplacian G x - 2 * H + 4 * V := by
    have h := hdq.deriv
    change dq = ((D.laplacian G x - 2 * H + 4 * V) * R x -
      G x * (D.laplacian R x + 2 * S x)) / R x ^ 2 at h
    rw [h]
    field_simp [hRx.ne']
    ring
  have hH : 0 ≤ H :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK : K ≤ Real.sqrt H * G x :=
    (le_abs_self K).trans (D.abs_hessian_quadratic_le_normSq (hRs x) (D.gradient R x))
  exact quotient_parabolic_bound (hR x) hH hK hgradient hspace htime

end PoincareConjecture.M47Positive
