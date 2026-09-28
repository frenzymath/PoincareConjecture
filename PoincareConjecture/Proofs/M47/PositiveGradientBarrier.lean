import PoincareConjecture.Proofs.M47.PositiveGradientReaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Coefficients

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M47Positive

section GeneralDimension

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_scalar_gradient_barrier (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hR : ∀ x, 0 < D.scalarCurvature x) (beta : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x =>
      g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
        D.scalarCurvature x + 240 * (D.ricciNormSq x - D.scalarCurvature x ^ 2 / 3) -
          beta * D.scalarCurvature x ^ 2) := by
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hGs := contMDiff_gradient_energy D hRs
  have hc (c : ℝ) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hdefect := hSs.sub ((hc (1 / 3)).smul (hRs.pow 2))
  have h := ((hGs.div₀ hRs (fun y => (hR y).ne')).add
    ((hc 240).smul hdefect)).sub ((hc beta).smul (hRs.pow 2))
  convert h using 1
  funext y
  change _ = g.inner y (D.gradient D.scalarCurvature y) (D.gradient D.scalarCurvature y) /
    D.scalarCurvature y + 240 * (D.ricciNormSq y - (1 / 3) * D.scalarCurvature y ^ 2) -
      beta * D.scalarCurvature y ^ 2
  ring

theorem continuousOn_scalar_gradient_barrier
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    (hR : ∀ t ∈ J, ∀ x, 0 < (F.connection t).scalarCurvature x) (beta : ℝ) :
    ContinuousOn (fun p : ℝ × M => (F.metric p.1).inner p.2
        ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2)
        ((F.connection p.1).gradient (F.connection p.1).scalarCurvature p.2) /
          (F.connection p.1).scalarCurvature p.2 +
      240 * ((F.connection p.1).ricciNormSq p.2 -
        (F.connection p.1).scalarCurvature p.2 ^ 2 / 3) -
      beta * (F.connection p.1).scalarCurvature p.2 ^ 2) (J ×ˢ univ) := by
  have hRjoint := (hC.scalar_regular n M J F).continuousOn
  have hSjoint := RicciFlowAnalysis.continuousOn_flow_ricciNormSq F
  have hGjoint := continuousOn_scalar_gradient_energy hC F
  exact ((hGjoint.div hRjoint (fun p hp => (hR p.1 hp.1 p.2).ne')).add
    (continuousOn_const.mul (hSjoint.sub ((hRjoint.pow 2).div_const 3)))).sub
      (continuousOn_const.mul (hRjoint.pow 2))

theorem differentiableAt_scalar_gradient_barrier
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hR : 0 < (F.connection t).scalarCurvature x) (beta : ℝ) :
    DifferentiableAt ℝ (fun s => (F.metric s).inner x
        ((F.connection s).gradient (F.connection s).scalarCurvature x)
        ((F.connection s).gradient (F.connection s).scalarCurvature x) /
          (F.connection s).scalarCurvature x +
      240 * ((F.connection s).ricciNormSq x - (F.connection s).scalarCurvature x ^ 2 / 3) -
        beta * (F.connection s).scalarCurvature x ^ 2) t := by
  have hdR := (hC.scalar_evolution n M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hdS := F.hasDerivAt_ricciNormSq hC ht x
  have hdG := hasDerivAt_scalar_gradient_energy hC F ht x
  exact (((hdG.div hdR hR.ne').add
    ((hdS.sub ((hdR.pow 2).div_const 3)).const_mul 240)).sub
      ((hdR.pow 2).const_mul beta)).differentiableAt

end GeneralDimension

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]

theorem scalar_gradient_barrier_evolution_le
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J)
    {t : ℝ} (ht : t ∈ interior J)
    (hR : ∀ y, 0 < (F.connection t).scalarCurvature y) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
      0 ≤ (F.connection t).ricci x v v)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    let H := fun s y => (F.metric s).inner y
      ((F.connection s).gradient (F.connection s).scalarCurvature y)
      ((F.connection s).gradient (F.connection s).scalarCurvature y) /
        (F.connection s).scalarCurvature y +
      240 * ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3) -
        beta * (F.connection s).scalarCurvature y ^ 2
    deriv (fun s => H s x) t ≤ (F.connection t).laplacian (H t) x +
      960 * (F.connection t).scalarCurvature x *
        ((F.connection t).ricciNormSq x - (F.connection t).scalarCurvature x ^ 2 / 3) -
      (4 * beta / 3) * (F.connection t).scalarCurvature x ^ 3 := by
  dsimp only
  let D := F.connection t
  let R := D.scalarCurvature
  let S := D.ricciNormSq
  let G := fun y => (F.metric t).inner y (D.gradient R y) (D.gradient R y)
  let q := fun s y => (F.metric s).inner y
    ((F.connection s).gradient (F.connection s).scalarCurvature y)
    ((F.connection s).gradient (F.connection s).scalarCurvature y) /
      (F.connection s).scalarCurvature y
  let H := fun s y => q s y +
    240 * ((F.connection s).ricciNormSq y - (F.connection s).scalarCurvature y ^ 2 / 3) -
      beta * (F.connection s).scalarCurvature y ^ 2
  let A := ∑ k, ∑ i, ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x
    ![(F.metric t).orthonormalBasis x k, (F.metric t).orthonormalBasis x i,
      (F.metric t).orthonormalBasis x j]) ^ 2
  let C := ∑ i, ∑ j, D.ricci x ((F.metric t).orthonormalBasis x i)
    ((F.metric t).orthonormalBasis x j) *
      (∑ a, ∑ c, D.curvatureTensor x ((F.metric t).orthonormalBasis x i)
        ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x j)
        ((F.metric t).orthonormalBasis x c) *
          D.ricci x ((F.metric t).orthonormalBasis x a) ((F.metric t).orthonormalBasis x c))
  let V := (F.metric t).inner x (D.gradient R x) (D.gradient S x)
  have hD := hC.tensor_calculus 3 M (F.metric t) D
  have hRs := hD.contMDiff_scalarCurvature
  have hSs := RicciFlow.contMDiff_ricciNormSq D hD
  have hGs := contMDiff_gradient_energy D hRs
  have hqs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (q t) :=
    hGs.div₀ hRs (fun y => (hR y).ne')
  have hc (c : ℝ) : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have hdef : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => S y - R y ^ 2 / 3) := by
    convert hSs.sub ((hc (1 / 3)).smul (hRs.pow 2)) using 1
    funext y
    change S y - R y ^ 2 / 3 = S y - (1 / 3) * R y ^ 2
    ring
  have hnorm := ricci_norm_bounds_of_nonneg D hD x hRic
  have hG : 0 ≤ G x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change 0 ≤ inner ℝ (D.gradient R x) (D.gradient R x)
    exact real_inner_self_nonneg
  have hS : 0 ≤ S x := (div_nonneg (sq_nonneg _) (by norm_num)).trans hnorm.1
  have hRx : 0 < R x := hR x
  have hV := scalar_ricci_gradient_pairing_le D hD x (hR x) hnorm.2
  have hV' : 4 / R x * V ≤ 4 * (A + G x) := by
    have h := mul_le_mul_of_nonneg_left hV (show 0 ≤ 4 / R x by positivity)
    change 4 / R x * V ≤ 4 / R x * (R x * (A + G x)) at h
    have hid : 4 / R x * (R x * (A + G x)) = 4 * (A + G x) := by
      field_simp [hRx.ne']
    rwa [hid] at h
  have hquot := scalar_gradient_quotient_evolution_le hC F ht hR x
  have hQ : deriv (fun s => q s x) t ≤ D.laplacian (q t) x + 4 * A + 4 * G x := by
    have hnon : 0 ≤ 2 * S x * G x / R x ^ 2 := by positivity
    change deriv (fun s => q s x) t ≤ D.laplacian (q t) x +
      4 / R x * V - 2 * S x * G x / R x ^ 2 at hquot
    linarith only [hquot, hV', hnon]
  have hdR := (hC.scalar_evolution 3 M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hdS := F.hasDerivAt_ricciNormSq hC ht x
  have hdG := hasDerivAt_scalar_gradient_energy hC F ht x
  have hdq := (hdG.div hdR hRx.ne').differentiableAt.hasDerivAt
  have htime := (((hdq.add ((hdS.sub ((hdR.pow 2).div_const 3)).const_mul 240))).sub
    ((hdR.pow 2).const_mul beta)).deriv
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at htime
  change deriv (fun s => H s x) t = deriv (fun s => q s x) t +
    240 * (D.laplacian S x - 2 * A + 4 * C -
      (2 * R x * (D.laplacian R x + 2 * S x)) / 3) -
    beta * (2 * R x * (D.laplacian R x + 2 * S x)) at htime
  have hspace : D.laplacian (H t) x = D.laplacian (q t) x +
    240 * (D.laplacian S x - (2 * R x * D.laplacian R x + 2 * G x) / 3) -
    beta * (2 * R x * D.laplacian R x + 2 * G x) := by
    have h240 : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => 240 * (S y - R y ^ 2 / 3)) :=
      (hc 240).smul hdef
    have hbetaR : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => beta * R y ^ 2) :=
      (hc beta).smul (hRs.pow 2)
    have hsum : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => q t y + 240 * (S y - R y ^ 2 / 3)) :=
      hqs.add h240
    have hthird : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => (1 / 3 : ℝ) * R y ^ 2) :=
      (hc (1 / 3)).smul (hRs.pow 2)
    change D.laplacian (fun y => q t y + 240 * (S y - R y ^ 2 / 3) - beta * R y ^ 2) x = _
    rw [D.laplacian_sub hsum hbetaR,
      D.laplacian_add hqs h240, D.laplacian_const_mul,
      D.laplacian_const_mul]
    have hdivide : (fun y => S y - R y ^ 2 / 3) =
        fun y => S y - (1 / 3 : ℝ) * R y ^ 2 := by funext y; ring
    rw [hdivide, D.laplacian_sub hSs hthird,
      D.laplacian_const_mul, D.laplacian_sq hRs]
    ring
  have hA := scalar_gradient_le_ricci_derivative D hD x
  have hbetaG := mul_le_mul_of_nonneg_right hbeta1 hG
  have hreact := ricci_defect_reaction_le D hD x (hR x) hRic
  have hscalar := mul_le_mul_of_nonneg_left hnorm.1
    (show 0 ≤ 4 * beta * R x by positivity)
  change deriv (fun s => H s x) t ≤ D.laplacian (H t) x +
    960 * R x * (S x - R x ^ 2 / 3) - (4 * beta / 3) * R x ^ 3
  change (7 / 20 : ℝ) * G x ≤ A at hA
  change 4 * C - (4 / 3) * R x * S x ≤ 4 * R x * (S x - R x ^ 2 / 3) at hreact
  nlinarith only [htime, hspace, hQ, hA, hG, hbetaG, hreact, hscalar]

end PoincareConjecture.M47Positive
