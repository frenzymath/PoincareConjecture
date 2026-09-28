import PoincareConjecture.Proofs.M47.PositiveWeightedAlgebra
import PoincareConjecture.Proofs.M47.PositiveScalarPowers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientMaximum
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Linearity

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M47Positive

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem gradient_const_mul (D : LeviCivitaData g)
    (c : ℝ) (f : M → ℝ) (x : M) :
    D.gradient (fun y => c * f y) x = c • D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  rw [D.inner_gradient, mvfderiv_const_mul]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]

theorem contMDiff_weighted_ricci_defect (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hR : ∀ x, 0 < D.scalarCurvature x) (p : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y =>
      (D.ricciNormSq y - D.scalarCurvature y ^ 2 / 3) / D.scalarCurvature y ^ p) := by
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 3 : ℝ)) :=
    contMDiff_const
  have hDs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => D.ricciNormSq y - D.scalarCurvature y ^ 2 / 3) := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, div_eq_mul_inv,
      one_mul, mul_comm] using hSs.sub (hc.smul (hRs.pow 2))
  exact hDs.div₀ (contMDiff_positive_rpow hRs hR p)
    (fun y => (Real.rpow_pos_of_pos (hR y) p).ne')

theorem weighted_ricci_gradient_bound (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hR : ∀ y, 0 < D.scalarCurvature y)
    (p : ℝ) {x : M}
    (hcrit : D.gradient (fun y =>
      (D.ricciNormSq y - D.scalarCurvature y ^ 2 / 3) / D.scalarCurvature y ^ p) x = 0) :
    (p * (D.ricciNormSq x - D.scalarCurvature x ^ 2 / 3) / D.scalarCurvature x +
        2 * D.scalarCurvature x / 3) ^ 2 *
      g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) ≤
      4 * D.ricciNormSq x *
        (∑ k, ∑ i, ∑ j,
          (D.covariantTensorDerivative D.ricciEvaluation x
            ![g.orthonormalBasis x k, g.orthonormalBasis x i, g.orthonormalBasis x j]) ^ 2) := by
  let R := D.scalarCurvature
  let q := fun y => (D.ricciNormSq y - R y ^ 2 / 3) / R y ^ p
  have hRs := hD.contMDiff_scalarCurvature
  have hPs := contMDiff_positive_rpow hRs hR p
  have hqs := contMDiff_weighted_ricci_defect D hD hR p
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 3 : ℝ)) :=
    contMDiff_const
  have hid : (fun y => q y * R y ^ p + (1 / 3 : ℝ) * (R y * R y)) =
      D.ricciNormSq := by
    funext y
    dsimp only [q]
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos (hR y) p).ne']
    ring
  have hgrad : D.gradient D.ricciNormSq x =
      (p * (D.ricciNormSq x - R x ^ 2 / 3) / R x + 2 * R x / 3) •
        D.gradient R x := by
    have h := D.gradient_add ((hqs.mul hPs x).mdifferentiableAt (by simp))
      ((hc.smul (hRs.mul hRs) x).mdifferentiableAt (by simp))
    change D.gradient (fun y => q y * R y ^ p + (1 / 3 : ℝ) * (R y * R y)) x =
      D.gradient (fun y => q y * R y ^ p) x +
        D.gradient (fun y => (1 / 3 : ℝ) * (R y * R y)) x at h
    rw [hid, D.gradient_mul ((hqs x).mdifferentiableAt (by simp))
      ((hPs x).mdifferentiableAt (by simp)), hcrit, smul_zero, add_zero,
      gradient_positive_rpow D hRs hR p, gradient_const_mul,
      D.gradient_mul ((hRs x).mdifferentiableAt (by simp))
        ((hRs x).mdifferentiableAt (by simp))] at h
    rw [h]
    simp only [smul_smul, ← add_smul]
    congr 1
    dsimp only [R]
    rw [Real.rpow_sub_one (hR x).ne']
    field_simp [(hR x).ne', (Real.rpow_pos_of_pos (hR x) p).ne']
    ring
  have hnorm : g.inner x (D.gradient D.ricciNormSq x) (D.gradient D.ricciNormSq x) =
      (p * (D.ricciNormSq x - R x ^ 2 / 3) / R x + 2 * R x / 3) ^ 2 *
        g.inner x (D.gradient R x) (D.gradient R x) := by
    rw [hgrad]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hpair : g.tensorPairingTwo D.ricciEvaluation D.ricciEvaluation = D.ricciNormSq := by
    funext y
    simp only [RiemannianMetric.tensorPairingTwo, LeviCivitaData.ricciNormSq,
      LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero, Matrix.cons_val_one, pow_two]
  have hK := D.gradient_tensor_normSq_le hD.2.1 x
  dsimp only at hK
  rw [hpair, hnorm] at hK
  simpa only [RiemannianMetric.tensorPairingThree, ← pow_two] using hK

private theorem weighted_time_nonpos {R S A G C U Lr Ls Lq dq p : ℝ}
    (hR : 0 < R) (hU : 0 < U) (hD : 0 ≤ S - R ^ 2 / 3) (hG : 0 ≤ G)
    (hp : 1 ≤ p) (hp' : p ≤ 2)
    (hK : (p * (S - R ^ 2 / 3) / R + 2 * R / 3) ^ 2 * G ≤ 4 * S * A)
    (hreact : (2 - p) * S * (S - R ^ 2 / 3) - (2 * S ^ 2 - 2 * R * C) ≤ 0)
    (hLq : Lq ≤ 0)
    (hspace : Ls - (2 / 3) * (R * Lr + G) =
      p * (S - R ^ 2 / 3) / R * Lr +
        p * (p - 1) * (S - R ^ 2 / 3) / R ^ 2 * G + U * Lq)
    (htime : dq * U + p * (S - R ^ 2 / 3) / R * (Lr + 2 * S) =
      Ls - 2 * A + 4 * C - (2 / 3) * R * (Lr + 2 * S)) : dq ≤ 0 := by
  have hgrad := weighted_gradient_remainder_nonpos hR hD hG hp hp' hK
  have hid : 4 * C - (4 / 3) * R * S - 2 * p * (S - R ^ 2 / 3) * S / R =
      2 * ((2 - p) * S * (S - R ^ 2 / 3) - (2 * S ^ 2 - 2 * R * C)) / R := by
    field_simp [hR.ne']
    ring
  have hr : 4 * C - (4 / 3) * R * S - 2 * p * (S - R ^ 2 / 3) * S / R ≤ 0 := by
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hreact)
      hR.le
  have hL := mul_nonpos_of_nonneg_of_nonpos hU.le hLq
  have hmul : dq * U ≤ 0 := by
    simp only [div_eq_mul_inv] at htime hspace hgrad hr
    nlinarith only [htime, hspace, hgrad, hr, hL]
  exact nonpos_of_mul_nonpos_left hmul hU

theorem differentiableAt_weighted_ricci_defect
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hR : 0 < (F.connection t).scalarCurvature x) (p : ℝ) :
    DifferentiableAt ℝ (fun s =>
      ((F.connection s).ricciNormSq x - (F.connection s).scalarCurvature x ^ 2 / 3) /
        (F.connection s).scalarCurvature x ^ p) t := by
  have hdR := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hdS := F.hasDerivAt_ricciNormSq hC ht x
  exact ((hdS.sub ((hdR.pow 2).div_const 3)).div
    (hdR.rpow_const (Or.inl hR.ne')) (Real.rpow_pos_of_pos hR p).ne').differentiableAt

theorem weighted_ricci_deriv_nonpos_at_localMax
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J)
    (hR : ∀ y, 0 < (F.connection t).scalarCurvature y)
    {p : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) {x : M}
    (hdefect : 0 ≤ (F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3)
    (hreact :
      let D := F.connection t
      let b := (F.metric t).orthonormalBasis x
      (2 - p) * D.ricciNormSq x * (D.ricciNormSq x - D.scalarCurvature x ^ 2 / 3) -
        (2 * D.ricciNormSq x ^ 2 - 2 * D.scalarCurvature x *
          (∑ i, ∑ j, D.ricci x (b i) (b j) *
            (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) *
              D.ricci x (b a) (b c)))) ≤ 0)
    (hmax : IsLocalMax (fun y =>
      ((F.connection t).ricciNormSq y - (F.connection t).scalarCurvature y ^ 2 / 3) /
        (F.connection t).scalarCurvature y ^ p) x) :
    deriv (fun s =>
      ((F.connection s).ricciNormSq x - (F.connection s).scalarCurvature x ^ 2 / 3) /
        (F.connection s).scalarCurvature x ^ p) t ≤ 0 := by
  let D := F.connection t
  let R := D.scalarCurvature
  let S := D.ricciNormSq
  let b := (F.metric t).orthonormalBasis x
  let A := ∑ k, ∑ i, ∑ j,
    (D.covariantTensorDerivative D.ricciEvaluation x ![b k, b i, b j]) ^ 2
  let C := ∑ i, ∑ j, D.ricci x (b i) (b j) *
    (∑ a, ∑ c, D.curvatureTensor x (b i) (b a) (b j) (b c) * D.ricci x (b a) (b c))
  let G := (F.metric t).inner x (D.gradient R x) (D.gradient R x)
  let U := R x ^ p
  let q := fun s y =>
    ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3) /
      (F.connection s).scalarCurvature y ^ p
  have hD := hC.tensor_calculus n M (F.metric t) D
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hPs := contMDiff_positive_rpow hRs hR p
  have hqs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q t) :=
    contMDiff_weighted_ricci_defect D hD hR p
  have hcrit : D.gradient (q t) x = 0 := by
    simp only [LeviCivitaData.gradient,
      LeviCivitaData.mvfderiv_eq_zero_of_isLocalMax hqs hmax, map_zero]
  have hLq := D.laplacian_nonpos_of_isLocalMax hqs hmax
  have hK := weighted_ricci_gradient_bound D hD hR p hcrit
  have hG : 0 ≤ G := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change 0 ≤ inner ℝ (D.gradient R x) (D.gradient R x)
    exact real_inner_self_nonneg
  have hU : 0 < U := Real.rpow_pos_of_pos (hR x) p
  have hRx : 0 < R x := hR x
  have hUne : R x ^ p ≠ 0 := hU.ne'
  have hcoef1 : q t x * (p * R x ^ (p - 1)) = p * (S x - R x ^ 2 / 3) / R x := by
    change (S x - R x ^ 2 / 3) / R x ^ p * (p * R x ^ (p - 1)) = _
    rw [Real.rpow_sub_one hRx.ne']
    field_simp [hRx.ne', hUne]
  have hcoef2 : q t x * (p * (p - 1) * R x ^ (p - 2)) =
      p * (p - 1) * (S x - R x ^ 2 / 3) / R x ^ 2 := by
    change (S x - R x ^ 2 / 3) / R x ^ p * (p * (p - 1) * R x ^ (p - 2)) = _
    rw [Real.rpow_sub hRx p 2, Real.rpow_two]
    field_simp [hRx.ne', hUne]
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 3 : ℝ)) :=
    contMDiff_const
  have hR2 : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => (1 / 3 : ℝ) * R y ^ 2) :=
    hc.smul (hRs.pow 2)
  have hprod : (fun y => q t y * R y ^ p) = fun y => S y - (1 / 3 : ℝ) * R y ^ 2 := by
    funext y
    change (S y - R y ^ 2 / 3) / R y ^ p * R y ^ p = _
    rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos (hR y) p).ne']
    ring
  have hspace : D.laplacian S x - (2 / 3) * (R x * D.laplacian R x + G) =
      p * (S x - R x ^ 2 / 3) / R x * D.laplacian R x +
        p * (p - 1) * (S x - R x ^ 2 / 3) / R x ^ 2 * G +
          U * D.laplacian (q t) x := by
    have h := D.laplacian_mul hqs hPs x
    change D.laplacian (fun y => q t y * R y ^ p) x =
      q t x * D.laplacian (fun y => R y ^ p) x +
        U * D.laplacian (q t) x +
        2 * (F.metric t).inner x (D.gradient (q t) x)
          (D.gradient (fun y => R y ^ p) x) at h
    rw [hprod, D.laplacian_sub hSs hR2,
      D.laplacian_const_mul, D.laplacian_sq hRs,
      laplacian_positive_rpow D hRs hR p, hcrit] at h
    simp only [map_zero, zero_apply, mul_zero, add_zero] at h
    change D.laplacian S x - (1 / 3) * (2 * R x * D.laplacian R x + 2 * G) =
      q t x * (p * R x ^ (p - 1) * D.laplacian R x +
        p * (p - 1) * R x ^ (p - 2) * G) + U * D.laplacian (q t) x at h
    linear_combination h + (D.laplacian R x) * hcoef1 + G * hcoef2
  have hdR := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  change HasDerivAt (fun s => (F.connection s).scalarCurvature x)
    (D.laplacian R x + 2 * S x) t at hdR
  have hdS := F.hasDerivAt_ricciNormSq hC ht x
  change HasDerivAt (fun s => (F.connection s).ricciNormSq x)
    (D.laplacian S x - 2 * A + 4 * C) t at hdS
  have hdP := hdR.rpow_const (p := p) (Or.inl (hR x).ne')
  have hdq := (hdS.sub ((hdR.pow 2).div_const 3)).div hdP hU.ne'
  change HasDerivAt (fun s => q s x) _ t at hdq
  have htime : deriv (fun s => q s x) t * U +
      p * (S x - R x ^ 2 / 3) / R x * (D.laplacian R x + 2 * S x) =
      D.laplacian S x - 2 * A + 4 * C - (2 / 3) * R x * (D.laplacian R x + 2 * S x) := by
    rw [hdq.deriv]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply, Pi.pow_apply]
    change (((D.laplacian S x - 2 * A + 4 * C -
      (2 * R x * (D.laplacian R x + 2 * S x)) / 3) * R x ^ p -
        (S x - R x ^ 2 / 3) * ((D.laplacian R x + 2 * S x) * p * R x ^ (p - 1))) /
          (R x ^ p) ^ 2) * R x ^ p + _ = _
    rw [Real.rpow_sub_one hRx.ne']
    field_simp [hRx.ne', hUne]
    ring
  exact weighted_time_nonpos (hR x) hU hdefect hG hp hp' hK hreact hLq hspace htime

end PoincareConjecture.M47Positive
