import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.AreaEstimates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}
  (D : LeviCivitaData g)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  {I : Set ℝ} (hI : IsOpen I)
  (hproper : IsProperMap (I.restrictPreimage f))
  (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

include hI hproper hreg

theorem regularLevelArea_error_le_of_power_bound
    {a b α : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hn : 2 ≤ n) (hα : 0 ≤ α) (hslab : Icc a b ⊆ I)
    (harea : ∀ t ∈ Icc a b, g.regularLevelArea hf t ≤ α * t ^ n) :
    (b - a) + n * (1 + α) *
        (∫ t in a..b, g.regularLevelArea hf t * (α / t) ^ 2) -
      (∫ t in a..b,
        (∫ z, D.levelMeanCurvature f
            (openLevelIncl f (g.regularDomain hf) t z) /
          g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
            (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))
          ∂g.regularLevelVolume hf (g.regularDomain hf)
            (g.regularDomain_regular hf) t) * (α / t)) ≤
        1 + n * (1 + α) * α ^ 3 + α ^ 2 := by
  obtain ⟨hsmooth, hderiv⟩ := D.first_variation_regularLevelArea hf hI hproper hreg
  have hc := hsmooth.continuousOn.mono hslab
  have hd := (hsmooth.differentiableOn (by simp)).mono (Ioo_subset_Icc_self.trans hslab)
  have hi : IntervalIntegrable (deriv (g.regularLevelArea hf)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact (hsmooth.continuousOn_deriv_of_isOpen hI (by simp)).mono hslab
  have hbound := Poincare.CurvatureIntegral.area_error_le_of_power_bound ha hab hb hn hα hc hd hi
    (fun t ht => ⟨g.regularLevelArea_nonneg hf t, harea t ht⟩)
  have heq : (∫ t in a..b, deriv (g.regularLevelArea hf) t * (α / t)) =
      ∫ t in a..b,
        (∫ z, D.levelMeanCurvature f
            (openLevelIncl f (g.regularDomain hf) t z) /
          g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
            (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))
          ∂g.regularLevelVolume hf (g.regularDomain hf)
            (g.regularDomain_regular hf) t) * (α / t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [(hderiv t (hslab ht)).deriv]
  rwa [heq] at hbound

theorem regularLevelArea_le_mul_one_add_of_forall_le_sub_meanCurvature
    {b α C K S : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hn : 1 ≤ n)
    (hα : 0 ≤ α) (hK : 0 ≤ K) (hslab : Icc b (3 * b / 2) ⊆ I)
    (harea : g.regularLevelArea hf b ≤ α * b ^ n)
    (hS : ∀ t ∈ Ioo b (3 * b / 2), S ≤ C * (1 + K) -
      (∫ z, D.levelMeanCurvature f
          (openLevelIncl f (g.regularDomain hf) t z) /
        g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
          (g.gradient f (openLevelIncl f (g.regularDomain hf) t z))
        ∂g.regularLevelVolume hf (g.regularDomain hf)
          (g.regularDomain_regular hf) t)) :
    S ≤ (C + 2 * α) * (1 + K) := by
  obtain ⟨hsmooth, hderiv⟩ := D.first_variation_regularLevelArea hf hI hproper hreg
  apply Poincare.CurvatureIntegral.le_mul_one_add_of_forall_le_sub_deriv
    hb hb1 hn hα hK (hsmooth.continuousOn.mono hslab)
    ((hsmooth.differentiableOn (by simp)).mono (Ioo_subset_Icc_self.trans hslab))
    harea (g.regularLevelArea_nonneg hf (3 * b / 2))
  intro t ht
  rw [(hderiv t (hslab (Ioo_subset_Icc_self ht))).deriv]
  exact hS t ht

end PoincareConjecture.LeviCivitaData
