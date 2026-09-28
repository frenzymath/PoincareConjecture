import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.RadialConvexity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.LocalIsometry
import Mathlib.Analysis.Convex.Deriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold BigOperators

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {γ : ℝ → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}

theorem inner_zero_of_gauss
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (a b : EuclideanSpace ℝ (Fin n)) : g.inner 0 a b = inner ℝ a b := by
  have hB := (g.contDiffAt_euclideanCoefficients 0).differentiableAt (by simp)
  have hleft := (hB.hasFDerivAt.clm_apply (hasFDerivAt_id 0)).clm_apply
    (hasFDerivAt_const b 0)
  have hright := (hasFDerivAt_id (0 : EuclideanSpace ℝ (Fin n))).inner ℝ
    (hasFDerivAt_const b 0)
  have heq : (fun y => g.euclideanCoefficients y y b) =ᶠ[𝓝 0]
      (fun y => inner ℝ y b) := Filter.Eventually.of_forall fun y => hgauss y b
  have hd := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L a)
    (hleft.fderiv.symm.trans (heq.fderiv_eq.trans hright.fderiv))
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply,
    zero_apply, map_zero, zero_add, add_zero, id_eq,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, inner_zero_right,
    euclideanCoefficients] at hd
  convert! hd using 1

private theorem IsGeodesicOn.source_ode
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt γ (deriv γ t) t ∧ HasDerivAt (deriv γ)
      (-coordinateChristoffel g.euclideanCoefficients (γ t) (deriv γ t) (deriv γ t)) t := by
  have hcoeff : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext x a b
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, hcoeff, id_eq] using
    hγ.hasDerivAt_in_chart hI (γ t) (by simp) t ht

theorem IsGeodesicOn.deriv_ne_zero_of_endpoints_ne
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ I) (hne : γ a ≠ γ b)
    {t : ℝ} (ht : t ∈ Icc a b) : deriv γ t ≠ 0 := by
  intro hz
  let V := fun s => g.tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
  have hV (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt V 0 s :=
    hγ.hasDerivAt_tangentNorm_zero (hsub hs)
  have htzero : V t = 0 := by
    dsimp only [V]
    rw [mfderiv_eq_fderiv]
    change g.tangentNorm (γ t) (fderiv ℝ γ t (1 : ℝ)) = 0
    rw [fderiv_eq_smul_deriv, one_smul, hz]
    simp [tangentNorm]
  have hzero (s : ℝ) (hs : s ∈ Icc a b) : deriv γ s = 0 := by
    have hv := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hV r hr).hasDerivWithinAt)
      (fun r _ => show ‖(0 : ℝ)‖ ≤ 0 by simp) ht hs
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at hv
    have hvs : V s = 0 := hv.trans htzero
    dsimp only [V] at hvs
    rw [mfderiv_eq_fderiv] at hvs
    change g.tangentNorm (γ s) (fderiv ℝ γ s (1 : ℝ)) = 0 at hvs
    rw [fderiv_eq_smul_deriv, one_smul] at hvs
    by_contra hsne
    have hp : 0 < g.tangentNorm (γ s) (deriv γ s) :=
      Real.sqrt_pos.mpr (g.pos _ _ hsne)
    linarith
  have hends := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hγ.source_ode hI (hsub hs)).1.differentiableAt)
    (fun s hs => show ‖deriv γ s‖ ≤ 0 by rw [hzero s hs]; simp)
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at hends
  exact hne hends.symm

private theorem IsGeodesicOn.differentiableAt_deriv_norm_sq
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (deriv (fun s => ‖γ s‖ ^ 2)) t := by
  have heq : deriv (fun s => ‖γ s‖ ^ 2) =ᶠ[𝓝 t]
      (fun s => 2 * inner ℝ (γ s) (deriv γ s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact ((hγ.source_ode hI hs).1.norm_sq).deriv
  exact (((hγ.source_ode hI ht).1.differentiableAt.inner ℝ
    (hγ.source_ode hI ht).2.differentiableAt).const_mul 2).congr_of_eventuallyEq heq

theorem IsGeodesicOn.convexOn_norm_sq
    (D : LeviCivitaData g)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), g.inner 0 a b = inner ℝ a b)
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I)
    {S : Set ℝ} (hS : Convex ℝ S) (hsub : S ⊆ I) {K : ℝ}
    (hsmall : ∀ t ∈ S, ‖γ t‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ t ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (r • γ t) ≤ K) :
    ConvexOn ℝ S (fun t => ‖γ t‖ ^ 2) := by
  apply convexOn_of_deriv2_nonneg hS
  · intro t ht
    exact ((hγ.source_ode hI (hsub ht)).1.continuousAt.norm.pow 2).continuousWithinAt
  · intro t ht
    exact ((hγ.source_ode hI (hsub (interior_subset ht))).1.norm_sq).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hγ.differentiableAt_deriv_norm_sq hI
      (hsub (interior_subset ht))).differentiableWithinAt
  · intro t ht
    exact (sq_nonneg _).trans (hγ.norm_sq_le_deriv2_norm_sq D hgauss hnorm hI
      (hsub (interior_subset ht)) (hsmall t (interior_subset ht)) (hcurv t (interior_subset ht)))

theorem IsGeodesicOn.strictConvexOn_norm_sq
    (D : LeviCivitaData g)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), g.inner 0 a b = inner ℝ a b)
    (hγ : g.IsGeodesicOn γ I) (hI : IsOpen I) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ I) (hne : γ a ≠ γ b) {K : ℝ}
    (hsmall : ∀ t ∈ Icc a b, ‖γ t‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ t ∈ Icc a b, ∀ r ∈ Icc (0 : ℝ) 1,
      D.curvatureTensorNorm (r • γ t) ≤ K) :
    StrictConvexOn ℝ (Icc a b) (fun t => ‖γ t‖ ^ 2) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc a b)
  · intro t ht
    exact ((hγ.source_ode hI (hsub ht)).1.continuousAt.norm.pow 2).continuousWithinAt
  · intro t ht
    have ht' := interior_subset ht
    have hpos : 0 < ‖deriv γ t‖ ^ 2 := sq_pos_of_pos
      (norm_pos_iff.mpr (hγ.deriv_ne_zero_of_endpoints_ne hI hab hsub hne ht'))
    exact hpos.trans_le (hγ.norm_sq_le_deriv2_norm_sq D hgauss hnorm hI
      (hsub ht') (hsmall t ht') (hcurv t ht'))

theorem strictConvexOn_sum_norm_sq_of_geodesics
    (D : LeviCivitaData g)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), g.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), g.inner 0 a b = inner ℝ a b)
    {ι : Type*} (s : Finset ι) (q : ι → ℝ → EuclideanSpace ℝ (Fin n))
    (hgeo : ∀ i ∈ s, g.IsGeodesicOn (q i) I) (hI : IsOpen I)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    {j : ι} (hj : j ∈ s) (hne : q j a ≠ q j b) {K : ℝ}
    (hsmall : ∀ i ∈ s, ∀ t ∈ Icc a b, ‖q i t‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ i ∈ s, ∀ t ∈ Icc a b, ∀ r ∈ Icc (0 : ℝ) 1,
      D.curvatureTensorNorm (r • q i t) ≤ K) :
    StrictConvexOn ℝ (Icc a b) (fun t => ∑ i ∈ s, ‖q i t‖ ^ 2) := by
  have hc (i : ι) (hi : i ∈ s) := (hgeo i hi).convexOn_norm_sq D hgauss hnorm hI
    (convex_Icc a b) hsub (hsmall i hi) (hcurv i hi)
  have hjc := (hgeo j hj).strictConvexOn_norm_sq D hgauss hnorm hI hab hsub hne
    (hsmall j hj) (hcurv j hj)
  refine ⟨convex_Icc a b, ?_⟩
  intro x hx y hy hxy c d hcpos hdpos hcd
  have hlt := Finset.sum_lt_sum
    (fun i hi => (hc i hi).2 hx hy hcpos.le hdpos.le hcd)
    ⟨j, hj, hjc.2 hx hy hxy hcpos hdpos hcd⟩
  simpa only [Finset.sum_add_distrib, Finset.smul_sum] using hlt

end PoincareConjecture.RiemannianMetric
