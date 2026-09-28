import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.CompactDivergence
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerOrder
import PoincareConjecture.Proofs.M04.ScalarChainRule










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def fieldNormSq (g : RiemannianMetric n V) (X : V → V) (x : V) : ℝ :=
  g.inner x (X x) (X x)

def fieldTraceHessian {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (x : V) : V :=
  ∑ i, fieldHessian D X x (g.orthonormalBasis x i) (g.orthonormalBasis x i)

def fieldGradientSq {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (x : V) : ℝ :=
  ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
    (D.connection X x (g.orthonormalBasis x i))

theorem fieldNormSq_contDiff (g : RiemannianMetric n V) {X : V → V}
    (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (fieldNormSq g X) :=
  ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).clm_apply hX).clm_apply hX



theorem fieldTraceHessian_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} (hX : ContDiff ℝ ∞ X) : ContDiff ℝ ∞ (fieldTraceHessian D X) := by
  have he : fieldTraceHessian D X = fun x =>
      (∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j •
        fderiv ℝ (fderiv ℝ X) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
      rawFirstOrderCoefficient D x (fderiv ℝ X x) + rawZeroOrderCoefficient D x (X x) -
        rawRicciLinear D x (X x) := by
    funext x
    exact eq_sub_iff_add_eq.mpr (raw_vector_heat_full_coordinate_operator D hX x)
  rw [he]
  have hdX : ContDiff ℝ ∞ (fderiv ℝ X) := hX.fderiv_right (by simp)
  have hddX : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ X)) := hdX.fderiv_right (by simp)
  apply ContDiff.sub
  · apply ContDiff.add
    · apply ContDiff.add
      · apply ContDiff.sum
        intro i _
        apply ContDiff.sum
        intro j _
        exact (raw_inverseGram_entry_contDiff g i j).smul
          ((hddX.clm_apply contDiff_const).clm_apply contDiff_const)
      · exact (rawFirstOrderCoefficient_contDiff D).clm_apply hdX
    · exact (rawZeroOrderCoefficient_contDiff D).clm_apply hX
  · exact (rawRicciLinear_contDiff D).clm_apply hX

theorem raw_scalar_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g) :
    ContDiff ℝ ∞ D.scalarCurvature := by
  have he : D.scalarCurvature = fun x => ∑ i, ∑ j, (rawCoordinateGram g x)⁻¹ i j *
      D.ricci x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    funext (raw_scalar_eq_inverse_gram D)
  rw [he]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (raw_inverseGram_entry_contDiff g i j).mul (raw_ricci_pair_contDiff D _ _)

def fieldEntropySource {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (φ : ℝ → ℝ) (x : V) : ℝ :=
  2 * deriv φ (fieldNormSq g X x) * g.inner x (fieldTraceHessian D X x) (X x) -
    D.scalarCurvature x * φ (fieldNormSq g X x)

def fieldEntropyDissipation {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (φ : ℝ → ℝ) (x : V) : ℝ :=
  2 * deriv φ (fieldNormSq g X x) * fieldGradientSq D X x +
    deriv (deriv φ) (fieldNormSq g X x) * M04.scalarGradientSq g (fieldNormSq g X) x +
      D.scalarCurvature x * φ (fieldNormSq g X x)


theorem fieldEntropy_balance {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {φ : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ) (x : V) :
    D.laplacian (fun y => φ (fieldNormSq g X y)) x =
      fieldEntropySource D X φ x + fieldEntropyDissipation D X φ x := by
  rw [M04.laplacian_comp D isOpen_univ
    (fieldNormSq_contDiff g hX).contMDiff.contMDiffOn hφ (mem_univ x)]
  change deriv φ (fieldNormSq g X x) * D.laplacian (fun y => g.inner y (X y) (X y)) x +
    deriv (deriv φ) (fieldNormSq g X x) * M04.scalarGradientSq g (fieldNormSq g X) x = _
  rw [laplacian_field_normSq D X hX]
  dsimp only [fieldEntropySource, fieldEntropyDissipation, fieldTraceHessian, fieldGradientSq]
  ring

theorem fieldEntropyDissipation_nonneg {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (X : V → V) (φ : ℝ → ℝ) (x : V)
    (hφ : 0 ≤ φ (fieldNormSq g X x))
    (hφ' : 0 ≤ deriv φ (fieldNormSq g X x))
    (hφ'' : 0 ≤ deriv (deriv φ) (fieldNormSq g X x))
    (hR : 0 ≤ D.scalarCurvature x) : 0 ≤ fieldEntropyDissipation D X φ x := by
  have hgrad : 0 ≤ fieldGradientSq D X x := by
    apply Finset.sum_nonneg
    intro i _
    by_cases hz : D.connection X x (g.orthonormalBasis x i) = 0
    · simp [hz]
    · exact (g.pos x _ hz).le
  exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hφ') hgrad)
    (mul_nonneg hφ'' (Finset.sum_nonneg fun _ _ => sq_nonneg _))) (mul_nonneg hR hφ)

theorem fieldEntropySource_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {φ : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fieldEntropySource D X φ) := by
  have hq := fieldNormSq_contDiff g hX
  have hg := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  exact ((contDiff_const.mul ((contDiff_infty_iff_deriv.mp hφ).2.comp hq)).mul
    ((hg.clm_apply (fieldTraceHessian_contDiff D hX)).clm_apply hX)).sub
      ((raw_scalar_contDiff D).mul (hφ.comp hq))

theorem fieldEntropySource_hasCompactSupport {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} {φ : ℝ → ℝ}
    (hc : HasCompactSupport X) (hφ0 : φ 0 = 0) :
    HasCompactSupport (fieldEntropySource D X φ) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  apply hx
  simp [fieldEntropySource, fieldNormSq, image_eq_zero_of_notMem_tsupport hn, hφ0]

theorem fieldNormSq_hasCompactSupport (g : RiemannianMetric n V)
    {X : V → V} (hc : HasCompactSupport X) : HasCompactSupport (fieldNormSq g X) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  exact hx (by simp [fieldNormSq, image_eq_zero_of_notMem_tsupport hn])

theorem fieldEntropyDissipation_eq {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {φ : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ) :
    fieldEntropyDissipation D X φ =
      fun x => D.laplacian (fun y => φ (fieldNormSq g X y)) x - fieldEntropySource D X φ x := by
  funext x
  linarith only [fieldEntropy_balance D hX hφ x]

theorem fieldEntropyDissipation_contDiff {g : RiemannianMetric n V} (D : LeviCivitaData g)
    {X : V → V} {φ : ℝ → ℝ} (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fieldEntropyDissipation D X φ) := by
  rw [fieldEntropyDissipation_eq D hX hφ]
  have hc := D.contMDiff_laplacian (hφ.comp (fieldNormSq_contDiff g hX)).contMDiff
  exact (contDiffOn_univ.mp hc.contMDiffOn.contDiffOn).sub
    (fieldEntropySource_contDiff D hX hφ)

theorem fieldEntropyDissipation_hasCompactSupport {g : RiemannianMetric n V}
    (D : LeviCivitaData g) {X : V → V} {φ : ℝ → ℝ}
    (hX : ContDiff ℝ ∞ X) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport X) (hφ0 : φ 0 = 0) :
    HasCompactSupport (fieldEntropyDissipation D X φ) := by
  rw [fieldEntropyDissipation_eq D hX hφ]
  exact (D.hasCompactSupport_laplacian
    ((fieldNormSq_hasCompactSupport g hc).comp_left hφ0)).sub
      (fieldEntropySource_hasCompactSupport D hc hφ0)

end PoincareConjecture.M35.Uniqueness.Heat
