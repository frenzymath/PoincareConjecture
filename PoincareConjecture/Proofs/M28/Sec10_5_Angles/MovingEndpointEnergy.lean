import PoincareConjecture.Proofs.M28.Sec10_5_Angles.MovingEndpointVariation
import PoincareConjecture.Proofs.M28.Mathlib.LocalParameterIntegral
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Geodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.PieceDeriv
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.MinimalVariation

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.M28.Comparison

open CoordinateExponential ConnectionVariation ConnectionAlongCurve
  ConjugateVariation Conjugate.Realization

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_inner_self_nonneg (g : RiemannianMetric n M)
    (p : M) (v : TangentSpace (𝓡 n) p) : 0 ≤ g.inner p v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos p v hv).le

private theorem MovingEndpointRealization.source
    {g : RiemannianMetric n M} {γ β : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (R : MovingEndpointRealization g γ β V a b)
    {i : ℕ} (hi : i < R.N) {t : ℝ}
    (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
    γ t ∈ (extChartAt (𝓡 n) (R.α i)).source :=
  R.base_source i hi t
    ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩

private theorem MovingEndpointRealization.time_subset
    {g : RiemannianMetric n M} {γ β : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (R : MovingEndpointRealization g γ β V a b)
    {i : ℕ} (hi : i < R.N) : Icc (R.τ i) (R.τ (i + 1)) ⊆ Icc a b := by
  intro t ht
  exact ⟨(R.time_mem i (by omega)).1.trans ht.1,
    ht.2.trans (R.time_mem (i + 1) (by omega)).2⟩

set_option maxHeartbeats 600000 in

theorem MovingEndpointRealization.exists_energy_support [T2Space M]
    {g : RiemannianMetric n M} {γ β : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)}
    (R : MovingEndpointRealization g γ β V 0 1) (D : LeviCivitaData g)
    {I : Set ℝ} (hsub : Icc (0 : ℝ) 1 ⊆ I) (hgeo : g.IsGeodesicOn γ I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) V) t)
    {L C : ℝ}
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = L)
    (hindex : ∀ t ∈ Icc (0 : ℝ) 1, intrinsicIndexIntegrand g D γ V t ≤ C) :
    ∃ H : ℝ → ℝ, ContDiffAt ℝ 2 H 0 ∧ H 0 = L ^ 2 ∧
      (∀ᶠ s in 𝓝 (0 : ℝ), g.edist (γ 0) (β s) ≠ ⊤ ∧
        (g.edist (γ 0) (β s)).toReal ^ 2 ≤ H s) ∧
      deriv (deriv H) 0 ≤ 2 * C := by
  classical
  let B := fun i => g.pullbackCoefficients (extChartAt (𝓡 n) (R.α i)).symm
  let A := fun i => christoffelBilinear (B i)
  let E : ℕ → ℝ → ℝ := fun i s =>
    ∫ t in (R.τ i)..(R.τ (i + 1)), energyDensity (B i) (R.u i) (0, 1) (s, t)
  let J : ℕ → ℝ := fun i =>
    ∫ t in (R.τ i)..(R.τ (i + 1)), chartIndexIntegrand (B i) (A i) (R.u i) t
  let S : ℝ → ℝ := fun s => ∑ i ∈ Finset.range R.N, E i s
  let H : ℝ → ℝ := fun s => 2 * S s
  have hτ (i : ℕ) (_hi : i < R.N) : R.τ i ≤ R.τ (i + 1) := (R.strict i).le
  have hG (i : ℕ) : ContDiffOn ℝ 2 (B i) (extChartAt (𝓡 n) (R.α i)).target :=
    (g.contDiffOn_chartCoefficients (R.α i)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hA (i : ℕ) : ContDiffOn ℝ 1 (A i) (extChartAt (𝓡 n) (R.α i)).target := by
    intro x hx
    have hxA : ContDiffAt ℝ ∞ (A i) x := contDiffAt_christoffelBilinear
      ((g.contDiffOn_chartCoefficients (R.α i)).contDiffAt
        ((isOpen_extChartAt_target (R.α i)).mem_nhds hx))
      (g.isInvertible_chartCoefficients (R.α i) hx)
    exact (hxA.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).contDiffWithinAt
  have htube (i : ℕ) (hi : i < R.N) :
      ∀ p ∈ Ioo (-R.ε) R.ε ×ˢ Ioo (R.τ i - R.ε) (R.τ (i + 1) + R.ε),
        R.u i p ∈ (extChartAt (𝓡 n) (R.α i)).target := by
    intro p hp
    exact R.tube i hi p ⟨hp.1,
      ⟨by linarith [hp.2.1, R.ε_le_ρ], by linarith [hp.2.2, R.ε_le_ρ]⟩⟩
  have hE2 (i : ℕ) (hi : i < R.N) :
      ContDiffOn ℝ 2 (E i) (Ioo (-R.ε) R.ε) := by
    have hdensity : ContDiffOn ℝ 2 (energyDensity (B i) (R.u i) (0, 1))
        (Ioo ((0 : ℝ) - R.ε) (0 + R.ε) ×ˢ
          Ioo (R.τ i - R.ε) (R.τ (i + 1) + R.ε)) := by
      apply contDiffOn_energyDensity (hG i) (R.smooth i hi)
      intro p hp
      exact htube i hi p ⟨by simpa using hp.1, hp.2⟩
    simpa only [zero_sub, zero_add] using
      (contDiffOn_two_intervalIntegral_of_contDiffOn_box
        (F := fun s t => energyDensity (B i) (R.u i) (0, 1) (s, t))
        (hτ i hi) R.ε_pos hdensity)
  have hS2 : ContDiffOn ℝ 2 S (Ioo (-R.ε) R.ε) :=
    ContDiffOn.sum fun i hi => hE2 i (Finset.mem_range.mp hi)
  have h0 : (0 : ℝ) ∈ Ioo (-R.ε) R.ε := ⟨by linarith [R.ε_pos], R.ε_pos⟩
  have hH2 : ContDiffAt ℝ 2 H 0 :=
    contDiffAt_const.mul (hS2.contDiffAt (isOpen_Ioo.mem_nhds h0))
  have htelescope (m : ℕ) :
      (∑ i ∈ Finset.range m, (R.τ (i + 1) - R.τ i)) = R.τ m - R.τ 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hsumτ : (∑ i ∈ Finset.range R.N, (R.τ (i + 1) - R.τ i)) = 1 := by
    simpa only [R.left, R.right, sub_zero] using htelescope R.N
  have hzero (i : ℕ) (hi : i < R.N) (t : ℝ)
      (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
      energyDensity (B i) (R.u i) (0, 1) (0, t) = (1 / 2 : ℝ) * L ^ 2 := by
    rw [energyDensity_eq_half_tangentNorm_sq g (R.α i)
      ((hgeo.contMDiffAt (hsub (R.time_subset hi ht))).mdifferentiableAt one_ne_zero)
      (R.source hi ht) ((R.smooth i hi).differentiable (by norm_num) _)
      (R.base i hi t ht), hspeed t (R.time_subset hi ht)]
  have hE0 (i : ℕ) (hi : i < R.N) :
      E i 0 = (R.τ (i + 1) - R.τ i) * ((1 / 2 : ℝ) * L ^ 2) := by
    calc
      E i 0 = ∫ _t in (R.τ i)..(R.τ (i + 1)), (1 / 2 : ℝ) * L ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hzero i hi t (by simpa only [uIcc_of_le (hτ i hi)] using ht)
      _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]
  have hH0 : H 0 = L ^ 2 := by
    change 2 * (∑ i ∈ Finset.range R.N, E i 0) = L ^ 2
    calc
      _ = 2 * (∑ i ∈ Finset.range R.N,
          (R.τ (i + 1) - R.τ i) * ((1 / 2 : ℝ) * L ^ 2)) := by
        congr 1
        exact Finset.sum_congr rfl fun i hi => hE0 i (Finset.mem_range.mp hi)
      _ = 2 * ((∑ i ∈ Finset.range R.N, (R.τ (i + 1) - R.τ i)) *
          ((1 / 2 : ℝ) * L ^ 2)) := by rw [← Finset.sum_mul]
      _ = L ^ 2 := by rw [hsumτ]; ring
  have hjunction : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i < R.N,
      (extChartAt (𝓡 n) (R.α i)).symm (R.u i (s, R.τ i)) = R.η i s ∧
      (extChartAt (𝓡 n) (R.α i)).symm (R.u i (s, R.τ (i + 1))) = R.η (i + 1) s := by
    have hfinite : ∀ i ∈ Finset.range R.N, ∀ᶠ s in 𝓝 (0 : ℝ),
        (extChartAt (𝓡 n) (R.α i)).symm (R.u i (s, R.τ i)) = R.η i s ∧
        (extChartAt (𝓡 n) (R.α i)).symm (R.u i (s, R.τ (i + 1))) = R.η (i + 1) s := by
      intro i hi
      filter_upwards [R.junction_left i (Finset.mem_range.mp hi),
        R.junction_right i (Finset.mem_range.mp hi)] with s hs hs'
      exact ⟨hs.1 ▸ (extChartAt (𝓡 n) (R.α i)).left_inv hs.2,
        hs'.1 ▸ (extChartAt (𝓡 n) (R.α i)).left_inv hs'.2⟩
    simpa only [Finset.mem_range] using (eventually_all_finset (Finset.range R.N)).mpr hfinite
  have hmajor : ∀ᶠ s in 𝓝 (0 : ℝ), g.edist (γ 0) (β s) ≠ ⊤ ∧
      (g.edist (γ 0) (β s)).toReal ^ 2 ≤ H s := by
    filter_upwards [hjunction, isOpen_Ioo.mem_nhds h0] with s hj hs
    have hmem (i : ℕ) (hi : i < R.N) (t : ℝ)
        (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
        R.u i (s, t) ∈ (extChartAt (𝓡 n) (R.α i)).target :=
      R.tube i hi (s, t) ⟨hs,
        ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩⟩
    let σ : ℕ → ℝ → M := fun i =>
      (extChartAt (𝓡 n) (R.α i)).symm ∘ (fun t => R.u i (s, t))
    have hus (i : ℕ) (hi : i < R.N) : ContDiff ℝ 3 (fun t => R.u i (s, t)) :=
      (R.smooth i hi).comp (contDiff_const.prodMk contDiff_id)
    have hf (i : ℕ) (hi : i < R.N) (t : ℝ)
        (ht : t ∈ Icc (R.τ i) (R.τ (i + 1))) :
        ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) (R.α i)).symm (R.u i (s, t)) :=
      (contMDiffOn_extChartAt_symm (R.α i)).contMDiffAt
        ((isOpen_extChartAt_target (R.α i)).mem_nhds (hmem i hi t ht))
    have hσ (i : ℕ) (hi : i < R.N) :
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (σ i) (Icc (R.τ i) (R.τ (i + 1))) := by
      intro t ht
      exact (((hf i hi t ht).of_le (by simp)).comp t
        (((hus i hi).of_le (by norm_num)).contDiffAt.contMDiffAt)).contMDiffWithinAt
    have hc (i : ℕ) (hi : i < R.N) : ContinuousOn (fun t =>
        g.tangentNorm (σ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (σ i) t 1))
          (Icc (R.τ i) (R.τ (i + 1))) :=
      g.continuousOn_speed_chart_comp (R.α i)
        (fun _ _ => ((hus i hi).of_le (by norm_num)).contDiffAt) (hmem i hi)
    let l : ℕ → ℝ := fun i => ∫ t in (R.τ i)..(R.τ (i + 1)),
      g.tangentNorm (σ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (σ i) t 1)
    have hl (i : ℕ) (hi : i < R.N) : 0 ≤ l i :=
      intervalIntegral.integral_nonneg (hτ i hi) (fun _ _ => Real.sqrt_nonneg _)
    have hd (i : ℕ) (hi : i < R.N) :
        g.edist (R.η i s) (R.η (i + 1) s) ≤ ENNReal.ofReal (l i) := by
      rw [← (hj i hi).1, ← (hj i hi).2]
      exact g.edist_le_ofReal_integral_speed (hτ i hi) (hσ i hi) (hc i hi)
    have hdtotal : g.edist (γ 0) (β s) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range R.N, l i) := by
      simpa only [R.fixed_left, R.moving_right] using
        Poincare.VolumeComparison.Conjugate.edist_le_ofReal_sum
          g (fun i => R.η i s) l R.N hl hd
    have hfinite : g.edist (γ 0) (β s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdtotal
    refine ⟨hfinite, ?_⟩
    let d := (g.edist (γ 0) (β s)).toReal
    have hdnonneg : 0 ≤ d := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hdnonneg with hd0 | hdpos
    · have hEnonneg (i : ℕ) (hi : i < R.N) : 0 ≤ E i s := by
        apply intervalIntegral.integral_nonneg (hτ i hi)
        intro t ht
        change 0 ≤ (1 / 2 : ℝ) *
          B i (R.u i (s, t)) (fderiv ℝ (R.u i) (s, t) (0, 1))
            (fderiv ℝ (R.u i) (s, t) (0, 1))
        exact mul_nonneg (by norm_num) (metric_inner_self_nonneg g _ _)
      have hsumE : 0 ≤ S s := Finset.sum_nonneg fun i hi =>
        hEnonneg i (Finset.mem_range.mp hi)
      change d ^ 2 ≤ 2 * S s
      rw [← hd0]
      nlinarith
    · have hbound := Poincare.VolumeComparison.Conjugate.sum_chartEnergy_ge_of_minimizing_endpoints
        g R.τ R.α R.u (fun i => R.η i s) hdpos hτ R.smooth hmem
        (fun i hi => (hj i hi).1) (fun i hi => (hj i hi).2)
        (by simpa only [R.fixed_left, R.moving_right, R.left, R.right,
          sub_zero, one_mul] using (ENNReal.ofReal_toReal hfinite).symm)
      simp only [R.left, R.right, sub_zero, mul_one] at hbound
      change d ^ 2 ≤ 2 * S s
      change (1 / 2 : ℝ) * d ^ 2 ≤ S s at hbound
      linarith
  have hfirst (i : ℕ) (hi : i < R.N) (s : ℝ) (hs : s ∈ Ioo (-R.ε) R.ε) :
      HasDerivAt (E i) (deriv (E i) s) s :=
    (hasDerivAt_pieceEnergy (hτ i hi) R.ε_pos (hG i) (R.smooth i hi)
      (htube i hi) hs).differentiableAt.hasDerivAt
  have hsecond (i : ℕ) (hi : i < R.N) : HasDerivAt (deriv (E i)) (J i) 0 := by
    apply hasDerivAt_deriv_pieceEnergy_chartIndexIntegrand (hτ i hi) R.ε_pos
      (isOpen_extChartAt_target (R.α i)) (fun _ _ _ => g.symm _ _ _)
      (christoffelBilinear_chart_symm g (R.α i))
      (fun _ hx => isMetricCompatibleAt_chartCoefficients g (R.α i) hx)
      (hG i) (hA i) (R.smooth i hi) (htube i hi)
    · intro t ht
      exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.α i) hgeo
        (hsub (R.time_subset hi ht)) (R.source hi ht)
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_const s (0 : ℝ)).prodMk (hasDerivAt_id s))
        (R.base i hi t ht)
    · exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.α i) (R.junction_geodesic i)
        ⟨by linarith [R.δ_pos i], R.δ_pos i⟩ (R.junction_left i hi).self_of_nhds.2
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_id s).prodMk (hasDerivAt_const s (R.τ i)))
        ((R.junction_left i hi).mono fun _ h => h.1)
    · exact covDerivAlong_fderiv_eq_zero_of_geodesic g (R.α i)
        (R.junction_geodesic (i + 1))
        ⟨by linarith [R.δ_pos (i + 1)], R.δ_pos (i + 1)⟩
        (R.junction_right i hi).self_of_nhds.2
        (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
        (fun s => (hasDerivAt_id s).prodMk (hasDerivAt_const s (R.τ (i + 1))))
        ((R.junction_right i hi).mono fun _ h => h.1)
  have hSsecond : HasDerivAt (deriv S) (∑ i ∈ Finset.range R.N, J i) 0 :=
    hasDerivAt_deriv_sum R.ε_pos hfirst hsecond
  have hHder : deriv H =ᶠ[𝓝 (0 : ℝ)] fun s => 2 * deriv S s := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
    exact (((hS2.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt
      (by norm_num)).hasDerivAt.const_mul 2).deriv
  have hHsecond : deriv (deriv H) 0 = 2 * (∑ i ∈ Finset.range R.N, J i) :=
    ((hSsecond.const_mul 2).congr_of_eventuallyEq hHder).deriv
  have hJbound (i : ℕ) (hi : i < R.N) :
      J i ≤ (R.τ (i + 1) - R.τ i) * C := by
    have hCI : ContinuousOn (fun t => chartIndexIntegrand (B i) (A i) (R.u i) t)
        (Icc (R.τ i) (R.τ (i + 1))) :=
      continuousOn_chartIndexIntegrand (isOpen_extChartAt_target (R.α i))
        (hG i) (hA i) (R.smooth i hi)
        (fun t ht => R.tube i hi (0, t) ⟨h0,
          ⟨by linarith [ht.1, R.ρ_pos], by linarith [ht.2, R.ρ_pos]⟩⟩)
    have hCIint : IntervalIntegrable (fun t => chartIndexIntegrand (B i) (A i) (R.u i) t)
        volume (R.τ i) (R.τ (i + 1)) := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le (hτ i hi)] using hCI
    have hb := intervalIntegral.integral_mono_on (hτ i hi) hCIint
      (intervalIntegrable_const (c := C)) (fun t ht => by
        have hqt := contMDiffAt_of_isGeodesicOn hgeo (hsub (R.time_subset hi ht))
        have hVt := hV t (hsub (R.time_subset hi ht))
        have hVa := contDiffAt_chartField_change hqt (mem_extChartAt_source _)
          (R.source hi ht) hVt
        rw [chartIndexIntegrand_eq_intrinsic g D (R.α i) hqt (R.source hi ht)
          (hVa.differentiableAt (by simp))
          (((R.smooth i hi).of_le (by norm_num)).contDiffAt)
          (R.base i hi t ht) (R.field i hi t ht)]
        exact hindex t (R.time_subset hi ht))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hb
  have hJsum : (∑ i ∈ Finset.range R.N, J i) ≤ C := by
    calc
      _ ≤ ∑ i ∈ Finset.range R.N, (R.τ (i + 1) - R.τ i) * C :=
        Finset.sum_le_sum fun i hi => hJbound i (Finset.mem_range.mp hi)
      _ = (∑ i ∈ Finset.range R.N, (R.τ (i + 1) - R.τ i)) * C :=
        (Finset.sum_mul _ _ _).symm
      _ = C := by rw [hsumτ, one_mul]
  refine ⟨H, hH2, hH0, hmajor, ?_⟩
  rw [hHsecond]
  linarith

end PoincareConjecture.M28.Comparison
end
