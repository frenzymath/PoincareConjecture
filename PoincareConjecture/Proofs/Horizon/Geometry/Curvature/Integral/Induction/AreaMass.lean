import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Coarea
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)

theorem integral_regularLevelArea_eq_integral_gradient_norm
    {a b : ℝ} (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b,
      mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) :
    (∫ t in a..b, g.regularLevelArea hf t) =
      ∫ x in f ⁻¹' Icc a b, g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
  let U := g.regularDomain hf
  have hKU : f ⁻¹' Icc a b ⊆ U :=
    fun x hx => (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
  have heq := g.integral_coarea_compact_slab hf U (g.regularDomain_regular hf)
    hcompact hKU (g.continuous_tangentNorm_gradient hf).continuousOn
  rw [heq, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hinner : (∫ z,
      g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z)) /
        g.tangentNorm (openLevelIncl f U t z) (g.gradient f (openLevelIncl f U t z))
      ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) =
      ∫ _ : openLevelSet f U t, (1 : ℝ)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact div_self (ne_of_gt z.1.2)
  calc
    g.regularLevelArea hf t = ∫ _ : openLevelSet f U t, (1 : ℝ)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t := by
      simp only [integral_const, regularLevelArea, U, smul_eq_mul, mul_one]
    _ = _ := hinner.symm

theorem integral_regularLevelArea_le_modelVolume [PreconnectedSpace M]
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (n + 1)) x),
      -1 ≤ D.sectionalCurvature x v w)
    {I : Set ℝ} (hproper : IsProperMap (I.restrictPreimage f))
    (hreg : ∀ x, f x ∈ I → mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    {a b L R : ℝ} (hab : a ≤ b) (hslab : Icc a b ⊆ I)
    (hL : 0 ≤ L) (hR : 0 < R) (p : M)
    (hspeed : ∀ x ∈ f ⁻¹' Icc a b, g.tangentNorm x (g.gradient f x) ≤ L)
    (hball : f ⁻¹' Icc a b ⊆ g.ball p R) :
    (∫ t in a..b, g.regularLevelArea hf t) ≤ L * modelVolume (n + 1) 1 R := by
  have hcompact := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hslab
  rw [g.integral_regularLevelArea_eq_integral_gradient_norm hf hab hcompact
    (fun x hx => hreg x (hslab hx))]
  have hi := (g.continuous_tangentNorm_gradient hf).continuousOn.integrableOn_compact hcompact
    (μ := g.volumeMeasure)
  have hiL : IntegrableOn (fun _ : M => L) (f ⁻¹' Icc a b) g.volumeMeasure :=
    continuousOn_const.integrableOn_compact hcompact
  have hmass := setIntegral_mono_on hi hiL
    (isClosed_Icc.preimage hf.continuous).measurableSet hspeed
  rw [setIntegral_const, smul_eq_mul] at hmass
  have hvol := measureReal_mono hball (g.volumeMeasure_ball_lt_top hcomplete p R).ne
  have hmodel := g.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    p (Nat.succ_pos n) hcomplete D hsec hR
  calc
    (∫ x in f ⁻¹' Icc a b, g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) ≤
        g.volumeMeasure.real (f ⁻¹' Icc a b) * L := hmass
    _ ≤ g.volumeMeasure.real (g.ball p R) * L := mul_le_mul_of_nonneg_right hvol hL
    _ ≤ L * modelVolume (n + 1) 1 R := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmodel hL

end PoincareConjecture.RiemannianMetric
