import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Index
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Minimizing
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateFrame

open ConnectionAlongCurve ConnectionVariation CoordinateExponential
open Poincare.ODE.Jacobi

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem trace_coefficient (D : LeviCivitaData g)
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (hi : (P t).IsInvertible)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (coefficient g q P t).toLinearMap =
      D.ricci (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
  obtain ⟨L, hL⟩ := hi
  have heq : coefficient g q P t = D.radialCurvatureInFrame (q t) L
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) := by
    apply ContinuousLinearMap.ext
    intro u
    rw [coefficient, chartCoefficient_apply D P (mem_extChartAt_source _) hq]
    simp only [← hL, ContinuousLinearMap.inverse_equiv,
      LeviCivitaData.radialCurvatureInFrame_apply, ContinuousLinearEquiv.coe_coe]
    rfl
  rw [heq, D.trace_radialCurvatureInFrame]



theorem ricci_mul_speed_sq_le_of_minimizing [T2Space M]
    (D : LeviCivitaData g) {q : ℝ → M} {ε C k : ℝ}
    (hε : 0 < ε) (hgeo : g.IsGeodesicOn q (Ioo (-ε) (1 + ε)))
    (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = C)
    (hmin : g.edist (q 0) (q 1) = ENNReal.ofReal C)
    (hRic : ∀ t ∈ Icc (0 : ℝ) 1,
      k * C ^ 2 ≤ D.ricci (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) :
    k * C ^ 2 ≤ 10 * (n : ℝ) := by
  let a := -ε / 2
  let b := 1 + ε / 2
  have ha : a < 0 := by dsimp [a]; linarith
  have hb : 1 < b := by dsimp [b]; linarith
  have hab : a < b := ha.trans (zero_lt_one.trans hb)
  have hsub : Icc a b ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h01' := h01.trans Ioo_subset_Icc_self
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q (Ioo (-ε) (1 + ε)) :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
  have hqt := fun t ht => Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo
    (hsub (show t ∈ Icc a b from ht))
  obtain ⟨P, hi, hP, hp⟩ := exists_orthonormal_parallel_transport g hab
    isOpen_Ioo hq hsub
  let R := coefficient g q P
  have hRc : ContinuousOn R (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (contDiffAt_coefficient D isOpen_Ioo hq
      (hsub (h01' ht)) (hi t (h01' ht))
      (fun u => (hP t (h01' ht) u).1)).continuousAt.continuousWithinAt
  apply trace_lower_le_of_polynomial_index_nonneg hRc
  · intro t ht
    rw [trace_coefficient D (hi t (h01' ht)) (hqt t (h01' ht))]
    exact hRic t ht
  · intro i
    let e := EuclideanSpace.basisFun (Fin n) ℝ i
    let W := indexTestField e
    let W' := indexTestDeriv e
    let V := fun t => P t (W t)
    have hVs : ∀ t ∈ Ioo a b, ContDiffAt ℝ ∞ (chartField q (q t) V) t := by
      intro t ht
      exact contDiffAt_frame_field (fun u => (hP t (Ioo_subset_Icc_self ht) u).1)
        (testField_smooth e).contDiffAt
    have hleft : V 0 = 0 := by simp [V, W, indexTestFieldTo]
    have hright : V 1 = 0 := by simp [V, W, indexTestFieldTo]
    have hnonneg := Conjugate.Realization.index_nonneg_of_minimizing g D
      (V₀ := V) (V₁ := V) (a := 0) (c := 1 / 2) (b := 1)
      (by norm_num) (by norm_num) isOpen_Ioo h01
      (fun t ht => hgeo t (hsub (Ioo_subset_Icc_self ht)))
      hVs hVs rfl hleft hright hC hspeed
      (by simpa only [sub_zero, one_mul] using hmin)
    have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        ConjugateVariation.intrinsicIndexIntegrand g D q V t =
          indexIntegrand R W W' W W' t := by
      rw [indexIntegrand_frame_field D (h01 ht) hi (hqt t (h01' ht))
        (hP t (h01' ht)) (hp t (h01' ht)) (testField_smooth e).contDiffAt]
      simp only [indexIntegrand, (indexTestField_deriv e t).deriv, W, W', R]
    have hint : IntervalIntegrable (indexIntegrand R W W' W W')
        MeasureTheory.volume 0 1 := by
      apply intInt_indexIntegrand <;> rw [uIcc_of_le zero_le_one]
      exacts [hRc, (indexTestField_cont _).continuousOn,
        (indexTestDeriv_cont _).continuousOn, (indexTestField_cont _).continuousOn,
        (indexTestDeriv_cont _).continuousOn]
    have heq₀ : (∫ t in (0 : ℝ)..(1 / 2),
        ConjugateVariation.intrinsicIndexIntegrand g D q V t) =
        ∫ t in (0 : ℝ)..(1 / 2), indexIntegrand R W W' W W' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
      exact heq t ⟨ht.1, by linarith [ht.2]⟩
    have heq₁ : (∫ t in (1 / 2 : ℝ)..1,
        ConjugateVariation.intrinsicIndexIntegrand g D q V t) =
        ∫ t in (1 / 2 : ℝ)..1, indexIntegrand R W W' W W' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
      exact heq t ⟨by linarith [ht.1], ht.2⟩
    rw [heq₀, heq₁] at hnonneg
    have hmid : (1 / 2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint.mono_set (by
        simp only [uIcc_of_le zero_le_one, uIcc_of_le hmid.1]
        exact Icc_subset_Icc_right hmid.2))
      (hint.mono_set (by
        simp only [uIcc_of_le zero_le_one, uIcc_of_le hmid.2]
        exact Icc_subset_Icc_left hmid.1))] at hnonneg
    exact hnonneg

end PoincareConjecture.ConjugateFrame
