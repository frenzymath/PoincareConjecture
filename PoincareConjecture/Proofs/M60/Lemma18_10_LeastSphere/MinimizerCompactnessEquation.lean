import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessTarget
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityFlux



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

open ConnectionVariation

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suCompactEquationBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactEquationBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suCompactEquationTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suCompactEquationTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



def suCoordinateHessian (u : LoopPlane → E) (x : LoopPlane) (i j : Fin 2) : E :=
  fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b j)

private theorem coordinate_quadratic_fderiv
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : LoopPlane → E) (x d : LoopPlane)
    (hG : DifferentiableAt ℝ G (u x)) (hu : ContDiffAt ℝ 2 u x)
    (hsym : ∀ v w, G (u x) v w = G (u x) w v) :
    fderiv ℝ (fun y => ∑ k : Fin 2,
      G (u y) (fderiv ℝ u y (b k)) (fderiv ℝ u y (b k))) x d =
        ∑ k : Fin 2, fderiv ℝ G (u x) (fderiv ℝ u x d)
          (fderiv ℝ u x (b k)) (fderiv ℝ u x (b k)) +
        2 * ∑ k : Fin 2, G (u x) (fderiv ℝ u x (b k))
          (fderiv ℝ (fun y => fderiv ℝ u y (b k)) x d) := by
  have hdu (k : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (b k)) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hGu := hG.hasFDerivAt.comp x (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hGu.clm_apply (hdu k).hasFDerivAt).clm_apply (hdu k).hasFDerivAt)
  have hqd := hq.fderiv
  simp only [Function.comp_apply] at hqd
  rw [hqd]
  simp only [Fin.sum_univ_two, add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  rw [hsym (fderiv ℝ (fun y => fderiv ℝ u y (b 0)) x d),
    hsym (fderiv ℝ (fun y => fderiv ℝ u y (b 1)) x d)]
  ring



def suAlphaHessianTerm (G : E →L[ℝ] E →L[ℝ] ℝ)
    (v : Fin 2 → E) (H : Fin 2 → Fin 2 → E) (d : ℝ) : E :=
  (2 / d) • ∑ i : Fin 2, ∑ k : Fin 2, (G (v k) (H k i)) • v i



def suAlphaLowerTerm (Gamma : E →L[ℝ] E →L[ℝ] E)
    (G : E →L[ℝ] E →L[ℝ] ℝ) (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (v : Fin 2 → E) (lambda : ℝ) (dlambda : Fin 2 → ℝ) (d c : ℝ) : E :=
  -(∑ i : Fin 2, Gamma (v i) (v i)) - (c / d) •
    ∑ i : Fin 2, ((∑ k : Fin 2, DG (v i) (v k) (v k)) -
      (∑ k : Fin 2, G (v k) (v k)) * dlambda i / lambda) • v i

set_option maxHeartbeats 1200000 in




theorem suAlphaEquation_nearLaplacian
    (Gamma : E → E →L[ℝ] E →L[ℝ] E)
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : LoopPlane → E)
    (lambda : LoopPlane → ℝ) (x : LoopPlane) {rho c : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hG : DifferentiableAt ℝ G (u x))
    (hlambda : DifferentiableAt ℝ lambda x) (hl : 0 < lambda x) (hrho : 0 < rho)
    (hsym : ∀ v w, G (u x) v w = G (u x) w v)
    (hpos : ∀ v, 0 ≤ G (u x) v v)
    (heq : let q := fun y => (∑ k : Fin 2,
        G (u y) (fderiv ℝ u y (b k)) (fderiv ℝ u y (b k))) / lambda y
      ∑ i : Fin 2, covDerivAlong Gamma u
        (fun y => (rho ^ 2 + q y) ^ c • fderiv ℝ u y (b i)) (b i) x = 0) :
    let v := fun i : Fin 2 => fderiv ℝ u x (b i)
    let H := suCoordinateHessian u x
    let d := rho ^ 2 * lambda x + ∑ k : Fin 2, G (u x) (v k) (v k)
    (∑ i : Fin 2, H i i) + c • suAlphaHessianTerm (G (u x)) v H d =
      suAlphaLowerTerm (Gamma (u x)) (G (u x)) (fderiv ℝ G (u x)) v (lambda x)
        (fun i => fderiv ℝ lambda x (b i)) d c := by
  let Q := fun y => ∑ k : Fin 2,
    G (u y) (fderiv ℝ u y (b k)) (fderiv ℝ u y (b k))
  let q := fun y => Q y / lambda y
  let v := fun i : Fin 2 => fderiv ℝ u x (b i)
  let H := suCoordinateHessian u x
  let d := rho ^ 2 * lambda x + Q x
  have hdu (k : Fin 2) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (b k)) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hQ : DifferentiableAt ℝ Q x := DifferentiableAt.fun_sum (u := Finset.univ)
    (fun k _ => (((hG.comp x (hu.differentiableAt (by norm_num))).clm_apply
      (hdu k)).clm_apply (hdu k)))
  have hlinv := (hasDerivAt_inv hl.ne').comp_hasFDerivAt x hlambda.hasFDerivAt
  have hqd := hQ.hasFDerivAt.mul hlinv
  have hq : DifferentiableAt ℝ q x := by
    simpa only [q, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! hqd.differentiableAt
  have hQpos : 0 ≤ Q x := Finset.sum_nonneg fun k _ => hpos _
  have hd : 0 < d := by dsimp [d]; positivity
  have hweight : 0 < rho ^ 2 + q x := by
    have := div_nonneg hQpos hl.le
    dsimp [q]
    positivity
  have ht := suAlphaEquation_tension Gamma u (e := q) (rho := rho) (c := c)
    (b 0) (b 1) hq hu hweight (by simpa only [Fin.sum_univ_two, q, Q] using heq)
  have hqderiv (i : Fin 2) : fderiv ℝ q x (b i) =
      ((∑ k : Fin 2, fderiv ℝ G (u x) (v i) (v k) (v k)) +
        2 * ∑ k : Fin 2, G (u x) (v k) (H k i)) / lambda x -
        Q x * fderiv ℝ lambda x (b i) / lambda x ^ 2 := by
    have hqfun : q = Q * ((fun y => y⁻¹) ∘ lambda) := by
      funext y
      simp only [q, Pi.mul_apply, Function.comp_apply, div_eq_mul_inv]
    rw [hqfun, hqd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
    rw [coordinate_quadratic_fderiv G u x (b i) hG hu hsym]
    change _ = ((∑ k : Fin 2, fderiv ℝ G (u x) (v i) (v k) (v k)) +
      2 * ∑ k : Fin 2, G (u x) (v k) (H k i)) / lambda x -
        Q x * fderiv ℝ lambda x (b i) / lambda x ^ 2
    dsimp only [v, H, suCoordinateHessian]
    ring
  have hc (i : Fin 2) : c / (rho ^ 2 + q x) * fderiv ℝ q x (b i) =
      c / d * ((∑ k : Fin 2, fderiv ℝ G (u x) (v i) (v k) (v k)) -
        Q x * fderiv ℝ lambda x (b i) / lambda x) +
      c * (2 / d) * ∑ k : Fin 2, G (u x) (v k) (H k i) := by
    rw [hqderiv]
    dsimp only [q, d]
    field_simp [hl.ne', hd.ne']
    ring
  change (∑ i : Fin 2, H i i) + c • suAlphaHessianTerm (G (u x)) v H d =
    suAlphaLowerTerm (Gamma (u x)) (G (u x)) (fderiv ℝ G (u x)) v (lambda x)
      (fun i => fderiv ℝ lambda x (b i)) d c
  simp only [covDerivAlong] at ht
  change (H 0 0 + Gamma (u x) (v 0) (v 0)) +
    (H 1 1 + Gamma (u x) (v 1) (v 1)) = _ at ht
  simp only [smul_add, smul_smul, neg_mul] at ht
  rw [hc 0, hc 1] at ht
  calc
    _ = ((H 0 0 + Gamma (u x) (v 0) (v 0)) +
      (H 1 1 + Gamma (u x) (v 1) (v 1))) +
      c • suAlphaHessianTerm (G (u x)) v H d -
        (Gamma (u x) (v 0) (v 0) + Gamma (u x) (v 1) (v 1)) := by
          simp only [Fin.sum_univ_two]
          abel
    _ = _ := by
      rw [ht]
      simp only [suAlphaHessianTerm, suAlphaLowerTerm, Fin.sum_univ_two,
        smul_add, smul_smul, Q, v]
      module

end PoincareConjecture.M60
