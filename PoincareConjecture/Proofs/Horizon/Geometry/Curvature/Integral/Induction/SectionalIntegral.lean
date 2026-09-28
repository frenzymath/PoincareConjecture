import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.MeanCurvature

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.LeviCivitaData

section Pointwise

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}

def levelSectionalError (D : LeviCivitaData g) (f K : M → ℝ) (β : ℝ) (x : M) : ℝ :=
  K x + (max 0 (-D.levelMeanCurvature f x) + (n : ℝ) * β) * β

theorem levelSectionalError_nonneg (D : LeviCivitaData g)
    (f K : M → ℝ) {β : ℝ} (hβ : 0 ≤ β) {x : M} (hK : 0 ≤ K x) :
    0 ≤ D.levelSectionalError f K β x :=
  add_nonneg hK (mul_nonneg
    (add_nonneg (le_max_left _ _) (mul_nonneg (Nat.cast_nonneg n) hβ)) hβ)

theorem continuousOn_levelSectionalError_regularDomain (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {K : M → ℝ} (hK : ContinuousOn K (g.regularDomain hf)) (β : ℝ) :
    ContinuousOn (D.levelSectionalError f K β) (g.regularDomain hf) := by
  apply hK.add
  exact (((continuousOn_const (c := (0 : ℝ))).sup
    (D.continuousOn_levelMeanCurvature_regularDomain hf).neg).add
      continuousOn_const).mul continuousOn_const

theorem levelMeanCurvature_le_of_tangentialHessian (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hreg : 0 < D.levelQ f x) (β : ℝ)
    (hhess : ∀ v : TangentSpace (𝓡 (n + 1)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v) :
    D.levelMeanCurvature f x ≤ (n : ℝ) * β := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let N := D.levelUnitNormal f x
  let b := g.orthonormalBasis x
  have hN : g.inner x N N = 1 := by
    have hs := Real.sq_sqrt hreg.le
    have hr := (Real.sqrt_pos.2 hreg).ne'
    change g.inner x ((Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x)
      ((Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (D.levelQ f x))⁻¹ *
      ((Real.sqrt (D.levelQ f x))⁻¹ * D.levelQ f x) = 1
    field_simp
    exact hs.symm
  have hinner (v w : TangentSpace (𝓡 (n + 1)) x) :
      ⟪v, w⟫_ℝ = g.inner x v w := rfl
  have hproj : (∑ i, g.inner x (D.levelProjection f x (b i))
      (D.levelProjection f x (b i))) = (n : ℝ) := by
    have ht := Poincare.LinearAlgebra.trace_orthogonal_restriction b
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 (n + 1)) x))
      (fun _ _ => rfl) N hN
    simp only [ContinuousLinearMap.id_apply, hinner, hN] at ht
    change (∑ i, g.inner x (D.levelProjection f x (b i))
      (D.levelProjection f x (b i))) = (∑ i, g.inner x (b i) (b i)) - 1 at ht
    have hdiag (i) : g.inner x (b i) (b i) = 1 := by
      change ⟪b i, b i⟫_ℝ = 1
      simpa only [ite_true] using b.inner_eq_ite i i
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 (n + 1)) x) = n + 1 := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1
      simp
    simpa only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hdim, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right] using ht
  calc
    D.levelMeanCurvature f x ≤
        ∑ i, β * g.inner x (D.levelProjection f x (b i))
          (D.levelProjection f x (b i)) :=
      Finset.sum_le_sum fun i _ => hhess _ (D.inner_gradient_levelProjection hreg _)
    _ = β * ∑ i, g.inner x (D.levelProjection f x (b i))
        (D.levelProjection f x (b i)) := (Finset.mul_sum _ _ _).symm
    _ = (n : ℝ) * β := by rw [hproj]; ring

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem integral_levelSectionalError_eq
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t : ℝ} (ht : t ∈ I) {K : M → ℝ}
    (hKc : ContinuousOn K (g.regularDomain hf)) (β : ℝ) :
    (∫ z, D.levelSectionalError f K β (openLevelIncl f (g.regularDomain hf) t z)
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) =
      (∫ z, K (openLevelIncl f (g.regularDomain hf) t z)
        ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) +
      ((∫ z, max 0 (-D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z))
        ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) +
        (n : ℝ) * β * g.regularLevelArea hf t) * β := by
  let := isFiniteMeasure_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
  have hiK := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht hKc
  have hiH := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    ((continuousOn_const (c := (0 : ℝ))).sup
      (D.continuousOn_levelMeanCurvature_regularDomain hf).neg)
  dsimp only [Function.comp_def, Pi.neg_apply] at hiK hiH
  have hiC := integrable_const ((n : ℝ) * β)
    (μ := g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t)
  unfold levelSectionalError
  have hsplit := integral_add hiK ((hiH.add hiC).mul_const β)
  dsimp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_mul_const, integral_add hiH hiC, integral_const]
  simp only [RiemannianMetric.regularLevelArea, smul_eq_mul,
    mul_comm _ ((n : ℝ) * β)]

theorem integral_levelSectionalError_le
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t α β : ℝ} (ht : t ∈ I) (hα : 0 < α) (hβ : 0 ≤ β)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hhess : ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (n + 1)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v)
    (hspeed : ∀ x, f x = t →
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    (∫ z, D.levelSectionalError f K β (openLevelIncl f (g.regularDomain hf) t z)
      ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) ≤
      (∫ z, K (openLevelIncl f (g.regularDomain hf) t z)
        ∂g.regularLevelVolume hf (g.regularDomain hf) (g.regularDomain_regular hf) t) +
      (n : ℝ) * (1 + α) * β ^ 2 * g.regularLevelArea hf t -
        β * deriv (g.regularLevelArea hf) t := by
  have hH : ∀ x, f x = t → D.levelMeanCurvature f x ≤ (n : ℝ) * β := by
    intro x hx
    have hq : 0 < D.levelQ f x :=
      Real.sqrt_pos.mp ((g.tangentNorm_gradient_pos_iff f x).mpr
        (hreg x (by simpa only [hx] using ht)))
    exact D.levelMeanCurvature_le_of_tangentialHessian hq β (hhess x hx)
  have hb := mul_le_mul_of_nonneg_right
    (D.integral_neg_levelMeanCurvature_le_sub_deriv hf hI hproper hreg ht hα hβ
      hH hspeed) hβ
  rw [D.integral_levelSectionalError_eq hf hI hproper hreg ht hKc β]
  nlinarith

end Pointwise

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [IsManifold (𝓡 (m + 2)) ∞ M]
  {g : RiemannianMetric (m + 2) M}

theorem regularLevel_sectionalError_integral_le
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I)
    (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {t α β : ℝ} (ht : t ∈ I) (hα : 0 < α) (hβ : 0 ≤ β)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x ∈ g.regularDomain hf, 0 ≤ K x)
    (hambient : ∀ x, f x = t → ∀ a b : TangentSpace (𝓡 (m + 2)) x,
      g.inner x a a = 1 → g.inner x b b = 1 → g.inner x a b = 0 →
      -K x ≤ D.sectionalCurvature x a b)
    (hhess : ∀ x, f x = t → ∀ v : TangentSpace (𝓡 (m + 2)) x,
      g.inner x (D.gradient f x) v = 0 →
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v)
    (hspeed : ∀ x, f x = t →
      1 / α ≤ g.tangentNorm x (g.gradient f x) ∧
        g.tangentNorm x (g.gradient f x) ≤ 1) :
    let U := g.regularDomain hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
    letI := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
    ∀ D' : LeviCivitaData (RiemannianMetric.regularLevelMetric
      hf U (g.regularDomain_regular hf) t g),
      (∀ z : openLevelSet f U t,
        0 ≤ D.levelSectionalError f K β (openLevelIncl f U t z) ∧
        ∀ u v : TangentSpace (𝓡 (m + 1)) z,
          (RiemannianMetric.regularLevelMetric hf U (g.regularDomain_regular hf) t g).inner
            z u u = 1 →
          (RiemannianMetric.regularLevelMetric hf U (g.regularDomain_regular hf) t g).inner
            z v v = 1 →
          (RiemannianMetric.regularLevelMetric hf U (g.regularDomain_regular hf) t g).inner
            z u v = 0 →
          -D.levelSectionalError f K β (openLevelIncl f U t z) ≤
            D'.sectionalCurvature z u v) ∧
      Integrable (D.levelSectionalError f K β ∘ openLevelIncl f U t)
        (g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ∧
      (∫ z, D.levelSectionalError f K β (openLevelIncl f U t z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
        (∫ z, K (openLevelIncl f U t z)
          ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) +
        ((m + 1 : ℕ) : ℝ) * (1 + α) * β ^ 2 * g.regularLevelArea hf t -
          β * deriv (g.regularLevelArea hf) t := by
  let U := g.regularDomain hf
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
  letI := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
  dsimp only
  intro D'
  refine ⟨?_, integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    (D.continuousOn_levelSectionalError_regularDomain hf hKc β), ?_⟩
  · intro z
    refine ⟨D.levelSectionalError_nonneg f K hβ (hK _ z.1.2), ?_⟩
    intro u v hu hv huv
    have htangent (w : TangentSpace (𝓡 (m + 1)) z) :
        g.inner (openLevelIncl f U t z) (D.gradient f (openLevelIncl f U t z))
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U t) z w) = 0 := by
      have hrange := range_mfderiv_openLevelIncl hf U (g.regularDomain_regular hf)
        (m + 1) t z
      have hw : mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U t) z w ∈
          (mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f (openLevelIncl f U t z)).ker := by
        rw [← hrange]
        exact ⟨w, rfl⟩
      change mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f (openLevelIncl f U t z)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U t) z w) = 0 at hw
      rw [D.inner_gradient]
      have hw' := congrArg
        (fun q => NormedSpace.fromTangentSpace (f (openLevelIncl f U t z)) q) hw
      convert hw' using 1 <;>
        simp only [mvfderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
          map_zero] <;> rfl
    have hh (w : TangentSpace (𝓡 (m + 1)) z) :=
      hhess (openLevelIncl f U t z) z.2
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U t) z w) (htangent w)
    have hb := D.regularLevel_sectionalCurvature_lower_bound hf U
      (g.regularDomain_regular hf) t (K (openLevelIncl f U t z)) β hβ D' z
      (hambient _ z.2) hh u v hu hv huv
    simpa only [levelSectionalError, neg_add_rev, sub_eq_add_neg, add_comm] using hb
  · exact D.integral_levelSectionalError_le hf hI hproper hreg ht hα hβ hKc hhess hspeed

end PoincareConjecture.LeviCivitaData
