import PoincareConjecture.Proofs.M35.TerminalBlowup.ScalarReciprocalGradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.M35

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem scalar_radius_edist_le_pathELength
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x)
    (hreg : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature)
    {A H a b : ℝ} (hA : 0 ≤ A) (hab : a < b)
    (hgrad : ∀ x, H ≤ D.scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤
          A * D.scalarCurvature x ^ (3 / 2 : ℝ))
    (gamma : ℝ → M) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc a b))
    (hhigh : ∀ u ∈ Icc a b, H ≤ D.scalarCurvature (gamma u)) :
    edist (D.scalarCurvature (gamma a) ^ (-1 / 2 : ℝ))
      (D.scalarCurvature (gamma b) ^ (-1 / 2 : ℝ)) ≤
        ENNReal.ofReal (A / 2) * g.pathELength gamma a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let f (x : M) := D.scalarCurvature x ^ (-1 / 2 : ℝ)
  have hf (x : M) : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) 1 f x :=
    (Real.contDiffAt_rpow_const_of_ne (hpos x).ne').contMDiffAt.comp x
      ((hreg x).of_le (by simp))
  have hnorm (x : M) (v : TangentSpace (𝓡 3) x) : ‖v‖ = g.tangentNorm x v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  let eta := f ∘ gamma
  have heta : ContDiffOn ℝ 1 eta (Icc a b) := by
    apply contMDiffOn_iff_contDiffOn.mp
    have hfOn : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) 1 f univ :=
      fun x _ => (hf x).contMDiffWithinAt
    exact hfOn.comp hgamma (mapsTo_univ _ _)
  calc
    _ = ‖eta b - eta a‖ₑ := by
      rw [edist_comm, edist_eq_enorm_sub]
      rfl
    _ ≤ ∫⁻ u in Icc a b, ‖derivWithin eta (Icc a b) u‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc heta hab.le
    _ = ∫⁻ u in Icc a b,
        ‖mvfderivWithin 𝓘(ℝ, ℝ) eta (Icc a b) u 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mvfderivWithin,
        mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ u in Icc a b, ENNReal.ofReal (A / 2) *
        ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc a b) u 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      have hchain : mvfderivWithin 𝓘(ℝ, ℝ) eta (Icc a b) u =
          (mvfderiv (𝓡 3) f (gamma u)).comp
            (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc a b) u) := by
        apply mvfderiv_comp_mfderivWithin
        · exact (hf _).mdifferentiableAt one_ne_zero
        · exact hgamma.mdifferentiableOn one_ne_zero u hu
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc hab u hu
      rw [hchain, ContinuousLinearMap.comp_apply]
      have h := ENNReal.ofReal_le_ofReal
        (D.scalar_radius_directional_bound (gamma u) (hpos _)
          ((hreg _).mdifferentiableAt (by simp)) (hgrad _ (hhigh u hu))
          (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc a b) u 1))
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ A / 2)] at h
      simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs, f] using h
    _ = _ := by
      rw [RiemannianMetric.pathELength, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]




theorem scalar_radius_lower_on_ball
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hpos : ∀ x, 0 < D.scalarCurvature x)
    (hreg : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature)
    {A H K : ℝ} (hA : 0 < A) (hK : 0 < K) (hHK : H ≤ K)
    (hgrad : ∀ x, H ≤ D.scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
        |mvfderiv (𝓡 3) D.scalarCurvature x v| ≤
          A * D.scalarCurvature x ^ (3 / 2 : ℝ))
    {x y : M} (hx : D.scalarCurvature x ≤ K)
    (hy : y ∈ g.ball x (K ^ (-1 / 2 : ℝ) / A)) :
    K ^ (-1 / 2 : ℝ) / 2 ≤ D.scalarCurvature y ^ (-1 / 2 : ℝ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra hbad
  have hbad' : D.scalarCurvature y ^ (-1 / 2 : ℝ) < K ^ (-1 / 2 : ℝ) / 2 :=
    lt_of_not_ge hbad
  have hkpow : 0 < K ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hK _
  have hyK : K < D.scalarCurvature y := by
    by_contra hyK
    have hpow := Real.rpow_le_rpow_of_nonpos (hpos y) (le_of_not_gt hyK)
      (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    linarith
  obtain ⟨gamma, h0, h1, hgamma, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  let f (u : ℝ) := D.scalarCurvature (gamma u)
  have hcont : ContinuousOn f (Icc 0 1) := hreg.continuous.comp_continuousOn hgamma.continuousOn
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic K) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨c, hc, hlast⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isGreatest
      ⟨0, ⟨⟨le_rfl, zero_le_one⟩, by simpa only [mem_preimage, mem_Iic, f, h0] using hx⟩⟩
  have hc1 : c < 1 := by
    apply lt_of_le_of_ne hc.1.2
    intro heq
    have h := hc.2
    rw [heq] at h
    exact not_le_of_gt hyK (by simpa only [mem_preimage, mem_Iic, f, h1] using h)
  have hcK : f c = K := by
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hc1.le
      (hcont.mono (Icc_subset_Icc hc.1.1 le_rfl))
      ⟨hc.2, by simpa only [f, h1] using hyK.le⟩
    have huc : u ≤ c := hlast ⟨⟨hc.1.1.trans hu.1, hu.2⟩, hfu.le⟩
    simpa only [le_antisymm huc hu.1] using hfu
  have hhigh : ∀ u ∈ Icc c 1, H ≤ f u := by
    intro u hu
    by_cases huc : u = c
    · simpa only [huc, hcK] using hHK
    · have hcu : c < u := lt_of_le_of_ne hu.1 (Ne.symm huc)
      have hKu : K < f u := by
        by_contra h
        exact not_le_of_gt hcu
          (hlast ⟨⟨hc.1.1.trans hu.1, hu.2⟩, le_of_not_gt h⟩)
      exact hHK.trans hKu.le
  have hdist := scalar_radius_edist_le_pathELength g D hpos hreg hA.le hc1 hgrad gamma
    (hgamma.mono (Icc_subset_Icc hc.1.1 le_rfl)) hhigh
  have hmono : g.pathELength gamma c 1 ≤ g.pathELength gamma 0 1 :=
    Manifold.pathELength_mono hc.1.1 le_rfl
  have hupper : edist (K ^ (-1 / 2 : ℝ))
      (D.scalarCurvature y ^ (-1 / 2 : ℝ)) < ENNReal.ofReal (K ^ (-1 / 2 : ℝ) / 2) := by
    have h := hdist.trans (mul_le_mul_right hmono _)
    have hcK' : D.scalarCurvature (gamma c) = K := hcK
    rw [hcK', h1] at h
    have hstrict := ENNReal.mul_lt_mul_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hA))) ENNReal.ofReal_ne_top hlength
    have heq : ENNReal.ofReal (A / 2) * ENNReal.ofReal (K ^ (-1 / 2 : ℝ) / A) =
        ENNReal.ofReal (K ^ (-1 / 2 : ℝ) / 2) := by
      rw [← ENNReal.ofReal_mul (half_pos hA).le]
      congr 1
      field_simp
    exact (h.trans_lt hstrict).trans_eq heq
  have hlower : ENNReal.ofReal (K ^ (-1 / 2 : ℝ) / 2) ≤
      edist (K ^ (-1 / 2 : ℝ)) (D.scalarCurvature y ^ (-1 / 2 : ℝ)) := by
    rw [edist_dist, Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    have habs : 0 ≤ K ^ (-1 / 2 : ℝ) - D.scalarCurvature y ^ (-1 / 2 : ℝ) := by
      linarith
    rw [abs_of_nonneg habs]
    linarith
  exact not_lt_of_ge hlower hupper

end PoincareConjecture.M35
