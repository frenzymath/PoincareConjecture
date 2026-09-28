import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.RadialHessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.ManifoldJacobiPairing
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.RiemannianMetric

open CoordinateExponential ConnectionVariation ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem isGeodesicOn_ray_of_gauss
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (v : EuclideanSpace ℝ (Fin n)) :
    g.IsGeodesicOn (fun r : ℝ => r • v) univ := by
  have hB : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hΓ (r : ℝ) : coordinateChristoffel g.euclideanCoefficients (r • v) v v = 0 :=
    christoffelBilinear_radial_eq_zero_of_gauss hB g.inner_isInvertible g.symm hgauss v r
  have hcoeff : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext x a b
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  intro t _
  refine ⟨0, (fun r => r • v), (fun _ => v), Filter.Eventually.of_forall ?_⟩
  intro r
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq, PartialEquiv.refl_target, mem_univ,
    hcoeff, hΓ, neg_zero, true_and]
  exact ⟨by simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const v,
    hasDerivAt_const r v⟩

theorem radial_pairing_ge_half_norm_sq
    (D : LeviCivitaData g)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), g.inner 0 a b = inner ℝ a b)
    {K : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hxr : ‖x‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ r ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (r • x) ≤ K)
    (w : EuclideanSpace ℝ (Fin n)) :
    ‖w‖ ^ 2 / 2 ≤ g.inner x
      (w + coordinateChristoffel g.euclideanCoefficients x x w) w := by
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun r => r • x
  let J : (r : ℝ) → TangentSpace (𝓡 n) (q r) := fun r => r • w
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q univ :=
    contMDiffOn_iff_contDiffOn.mpr (by dsimp [q]; fun_prop)
  have hJ : ∀ r ∈ (univ : Set ℝ),
      ContDiffAt ℝ ∞ (chartField q (q r) J) r := by
    intro r _
    change ContDiffAt ℝ ∞ (fun s => mfderiv (𝓡 n) (𝓡 n) id (q s) (J s)) r
    simp only [mfderiv_id]
    change ContDiffAt ℝ ∞ J r
    dsimp [J]
    fun_prop
  have hjac : ∀ r ∈ (univ : Set ℝ),
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 r =
        -D.curvature (q r) (J r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) := by
    intro r _
    have hj := manifoldVariation_jacobi g D isOpen_univ isOpen_univ (mem_univ 0)
      (u := fun z : ℝ × ℝ => z.2 • (x + z.1 • w))
      (contMDiffOn_iff_contDiffOn.mpr (by fun_prop))
      (fun s _ => isGeodesicOn_ray_of_gauss hgauss (x + s • w)) (mem_univ r)
    have hjfield (r : ℝ) :
        mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => r • (x + s • w)) 0 1 = r • w := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun s : ℝ => r • (x + s • w)) 0 (1 : ℝ) = r • w
      rw [fderiv_eq_smul_deriv, one_smul]
      change deriv (fun s : ℝ => r • (x + s • w)) 0 = r • w
      have hd : HasDerivAt (fun s : ℝ => r • (x + s • w)) (r • w) 0 := by
        convert! ((hasDerivAt_const (0 : ℝ) x).add
          ((hasDerivAt_id (0 : ℝ)).smul_const w)).const_smul r using 1
        simp
      exact hd.deriv
    dsimp only at hj
    rw [show x + (0 : ℝ) • w = x by simp] at hj
    change manifoldCovDerivAlong g q
      (manifoldCovDerivAlong g q
        (fun r => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => r • (x + s • w)) 0 1) 1) 1 r +
      D.curvature (q r)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => r • (x + s • w)) 0 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) = 0 at hj
    simp only [hjfield] at hj
    exact eq_neg_of_add_eq_zero_left hj
  have hspeed (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (q r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) = ‖x‖ := by
    have hg := isGeodesicOn_ray_of_gauss hgauss x
    have hzero : g.tangentNorm (q 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = ‖x‖ := by
      rw [mfderiv_eq_fderiv]
      change g.tangentNorm (q 0) (fderiv ℝ q 0 (1 : ℝ)) = ‖x‖
      rw [fderiv_eq_smul_deriv, one_smul]
      have hd : HasDerivAt q x 0 := by
        simpa only [q, id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const x
      rw [hd.deriv]
      change Real.sqrt (g.inner (0 • x) x x) = ‖x‖
      rw [zero_smul, hnorm, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg x)]
    have hconst (s : ℝ) := hg.hasDerivAt_tangentNorm_zero (mem_univ s)
    have heq := isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun r _ => (hconst r).differentiableAt.differentiableWithinAt)
      (fun r _ => (hconst r).deriv) (mem_univ r) (mem_univ 0)
    exact heq.trans hzero
  have h := ManifoldJacobi.manifold_jacobi_half_inner_one_lower_bound D
    isOpen_univ hq hJ (subset_univ _) hjac hcurv hspeed hxr
    (show J 0 = 0 by simp [J])
  have hD0 : manifoldCovDerivAlong g q J 1 0 = w := by
    rw [LeviCivitaData.manifoldCovDerivAlong_model, covDerivAlong]
    have hd : HasDerivAt J w 0 := by
      simpa only [J, id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const w
    simp only [fderiv_eq_smul_deriv, one_smul, hd.deriv, J, zero_smul, map_zero, add_zero]
  have hD1 : manifoldCovDerivAlong g q J 1 1 =
      w + coordinateChristoffel g.euclideanCoefficients x x w := by
    rw [LeviCivitaData.manifoldCovDerivAlong_model]
    change covDerivAlong (christoffelBilinear g.euclideanCoefficients)
      (fun r : ℝ => r • x) (fun r : ℝ => r • w) 1 1 = _
    exact radial_covDerivAt_one _ _ _
  rw [hD0, hD1] at h
  change g.tangentNorm (q 0) w ^ 2 / 2 ≤
    g.inner (q 1) (w + coordinateChristoffel g.euclideanCoefficients x x w) (J 1) at h
  have hzero : g.tangentNorm (q 0) w = ‖w‖ := by
    change Real.sqrt (g.inner (0 • x) w w) = ‖w‖
    rw [zero_smul, hnorm, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [hzero] at h
  change ‖w‖ ^ 2 / 2 ≤ g.inner (1 • x)
    (w + coordinateChristoffel g.euclideanCoefficients x x w) (1 • w) at h
  have hbase := congrArg (fun z : EuclideanSpace ℝ (Fin n) =>
    g.inner z (w + coordinateChristoffel g.euclideanCoefficients x x w) w)
    (one_smul ℝ x)
  simp only [one_smul] at h
  exact h.trans_eq hbase

theorem IsGeodesicOn.norm_sq_le_deriv2_norm_sq
    (D : LeviCivitaData g)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), g.inner 0 a b = inner ℝ a b)
    {K : ℝ} {u : ℝ → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}
    (hgeo : g.IsGeodesicOn u I) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (hut : ‖u t‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ r ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (r • u t) ≤ K) :
    ‖deriv u t‖ ^ 2 ≤ (deriv^[2] (fun s => ‖u s‖ ^ 2)) t := by
  rw [hgeo.deriv2_norm_sq_eq_radial_pairing hI ht
    (Filter.Eventually.of_forall hgauss)]
  have h := radial_pairing_ge_half_norm_sq D hgauss hnorm hut hcurv (deriv u t)
  linarith

end PoincareConjecture.RiemannianMetric
