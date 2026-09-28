import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.RadialGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]


theorem exists_potential_distance_lower_bound
    (S : GradientShrinkingSolitonData 3 M) (p : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : M,
      S.potential p - C * (S.metric.edist p x).toReal +
        (S.metric.edist p x).toReal ^ 2 / 4 ≤ S.potential x := by
  obtain ⟨C, hC, hradial⟩ := S.exists_radial_derivative_lower_bound
  let G := S.metric.tangentNorm p (S.connection.gradient S.potential p)
  refine ⟨G + C, add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hC, ?_⟩
  intro x
  by_cases hpx : p = x
  · subst x
    let := S.metric.toMetricSpace
    have heq : S.metric.edist p p = 0 := by change edist p p = 0; exact edist_self p
    simp [heq]
  have hd : 0 < (S.metric.edist p x).toReal := by
    let := S.metric.toMetricSpace
    change 0 < dist p x
    exact dist_pos.mpr hpx
  let L := (S.metric.edist p x).toReal
  obtain ⟨γ, hγ0, hγL, hgeo, hspeed, hmin⟩ :=
    S.metric.exists_unit_speed_minimizing_geodesic_of_metricComplete S.complete p x hd
  let I : Set ℝ := {s | ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧ S.metric.IsGeodesicOn γ U}
  have hI : IsOpen I := by
    apply isOpen_iff_mem_nhds.mpr
    rintro s ⟨U, hU, hs, hgeoU⟩
    apply Filter.mem_of_superset (hU.mem_nhds hs)
    intro t ht
    exact ⟨U, hU, ht, hgeoU⟩
  have hsub : Icc 0 L ⊆ I := fun s hs => hgeo.exists_open_nhds hs
  have hgeoI : S.metric.IsGeodesicOn γ I := by
    rintro s ⟨U, hU, hs, hgeoU⟩
    exact hgeoU s hs
  have hF (s : ℝ) (hs : s ∈ I) : ContDiffAt ℝ 2 (S.potential ∘ γ) s :=
    contMDiffAt_iff_contDiffAt.mp ((S.potential_C2 _).comp s
      ((Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeoI hs).of_le (by norm_cast)))
  let q := deriv (S.potential ∘ γ)
  have hq : ContinuousOn q (Icc 0 L) := by
    intro s hs
    exact ((hF s (hsub hs)).derivWithin (m := 1)
      (by norm_num)).continuousAt.continuousWithinAt
  have hqbound (s : ℝ) (hs : s ∈ Icc 0 L) : q 0 + s / 2 - C ≤ q s := by
    apply hradial γ I s hI
      ((Icc_subset_Icc_right hs.2).trans hsub) hgeoI hs.1
      (fun t ht => hspeed t ((Icc_subset_Icc_right hs.2) ht))
    simpa only [zero_sub, abs_neg, abs_of_nonneg hs.1] using
      hmin 0 ⟨le_rfl, hd.le⟩ s hs
  have hFTC : (∫ s in (0 : ℝ)..L, q s) = S.potential (γ L) - S.potential (γ 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hd.le
      (fun s hs => ((hF s (hsub hs)).continuousAt).continuousWithinAt)
    · intro s hs
      exact ((hF s (hsub (Ioo_subset_Icc_self hs))).differentiableAt (by norm_num)).hasDerivAt
    · exact hq.intervalIntegrable_of_Icc hd.le
  have hIntegral : q 0 * L + L ^ 2 / 4 - C * L ≤
      S.potential x - S.potential p := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hd.le
      (((continuous_const.add (continuous_id.div_const 2)).sub continuous_const).intervalIntegrable 0 L)
      (hq.intervalIntegrable_of_Icc hd.le) hqbound
    change (∫ s in (0 : ℝ)..L, q 0 + s / 2 - C) ≤ ∫ s in (0 : ℝ)..L, q s at h
    rw [hFTC, hγL, hγ0] at h
    have hpoly : (∫ s in (0 : ℝ)..L, q 0 + s / 2 - C) =
        q 0 * L + L ^ 2 / 4 - C * L := by
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hd.le
        (f := fun s : ℝ => q 0 * s + s ^ 2 / 4 - C * s)
        (f' := fun s : ℝ => q 0 + s / 2 - C)
        (by fun_prop : ContinuousOn (fun s : ℝ => q 0 * s + s ^ 2 / 4 - C * s) (Icc 0 L))
        (fun s _ => by
          convert (((hasDerivAt_id s).const_mul (q 0)).add
            (((hasDerivAt_id s).pow 2).div_const 4)).sub
              ((hasDerivAt_id s).const_mul C) using 1
          · rfl
          · simp only [id_eq]
            ring)
        (((continuous_const.add (continuous_id.div_const 2)).sub continuous_const).intervalIntegrable 0 L)
      simpa using hi
    rw [hpoly] at h
    exact h
  have hq0 : -G ≤ q 0 := by
    have hγd := (hgeo.contMDiffAt (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hd.le⟩)).mdifferentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hder : HasDerivAt (S.potential ∘ γ)
        (mvfderiv (𝓡 3) S.potential (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1)) 0 :=
      (((S.potential_C2 _).mdifferentiableAt (by norm_num)).hasMFDerivAt.comp 0
        hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
    have h := S.connection.abs_mvfderiv_le_gradient_norm S.potential (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1)
    rw [hspeed 0 ⟨le_rfl, hd.le⟩, mul_one, ← hder.deriv, hγ0] at h
    exact (abs_le.mp h).1
  have hmul := mul_le_mul_of_nonneg_right hq0 hd.le
  change S.potential p - (G + C) * L + L ^ 2 / 4 ≤ S.potential x
  nlinarith only [hIntegral, hmul]


theorem isCompact_potential_sublevel
    (S : GradientShrinkingSolitonData 3 M) (a : ℝ) :
    IsCompact {x : M | S.potential x ≤ a} := by
  let p : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨C, hC, hbound⟩ := S.exists_potential_distance_lower_bound p
  let R := 8 * |a - S.potential p| + 16 * C ^ 2 + 1
  apply (S.metric.isCompact_closedBall_of_metricComplete S.complete p R).of_isClosed_subset
    (isClosed_le S.potential_C2.continuous continuous_const)
  intro x hx
  let d := (S.metric.edist p x).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have h := hbound x
  change S.potential x ≤ a at hx
  have hsq : d ^ 2 ≤ 8 * |a - S.potential p| + 16 * C ^ 2 := by
    have habs := le_abs_self (a - S.potential p)
    have hs := sq_nonneg (d - 4 * C)
    change S.potential p - C * d + d ^ 2 / 4 ≤ S.potential x at h
    nlinarith only [h, hx, habs, hs]
  have hdR : d ≤ R := by
    dsimp only [R]
    nlinarith [sq_nonneg (d - 1 / 2)]
  change S.metric.edist p x ≤ ENNReal.ofReal R
  rw [← ENNReal.ofReal_toReal (S.metric.edist_ne_top p x)]
  exact ENNReal.ofReal_le_ofReal hdR

end PoincareConjecture.GradientShrinkingSolitonData
