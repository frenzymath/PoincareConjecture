import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FixedArcLength
import PoincareConjecture.Proofs.M62.Cor0_3_Regularization
import Mathlib.Topology.MetricSpace.Pseudo.Basic











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)




theorem m63ArcCutoff_regularization_error (hc : M62ShrinkingCurve F c)
    {alpha beta : ℝ} (hab : alpha ≤ beta) (x0 r : ℝ)
    (psi : ℝ → ℝ) (hpsi : Continuous psi)
    (hpsiRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Icc a b) :
    let Iε := ∫ x in alpha..beta, psi (m63ArcLength F c t x0 x / r) *
      m62RegularizedCurvature F c ε t x * curveSpeed F c t x
    let I := ∫ x in alpha..beta, psi (m63ArcLength F c t x0 x / r) *
      m62Curvature F c t x * curveSpeed F c t x
    0 ≤ Iε - I ∧ Iε - I ≤ ε * m63ArcLength F c t alpha beta := by
  dsimp only
  let phi := fun x => psi (m63ArcLength F c t x0 x / r)
  let h := m62RegularizedCurvature F c ε t
  let k := m62Curvature F c t
  let v := curveSpeed F c t
  have hv : Continuous v := (speed_continuousOn F c hc).comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hh : Continuous h := (regularized_continuousOn F c hc ε).comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hk : Continuous k := (curvature_continuousOn F c hc).comp_continuous
    (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hsigma : Continuous (fun x => m63ArcLength F c t x0 x) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hv.integral_hasStrictDerivAt x0 x).hasDerivAt.continuousAt
  have hphi : Continuous phi := hpsi.comp (hsigma.div_const r)
  have hhi : IntervalIntegrable (fun x => phi x * h x * v x) volume alpha beta :=
    ((hphi.mul hh).mul hv).intervalIntegrable alpha beta
  have hki : IntervalIntegrable (fun x => phi x * k x * v x) volume alpha beta :=
    ((hphi.mul hk).mul hv).intervalIntegrable alpha beta
  change 0 ≤ (∫ x in alpha..beta, phi x * h x * v x) -
      (∫ x in alpha..beta, phi x * k x * v x) ∧
    (∫ x in alpha..beta, phi x * h x * v x) -
      (∫ x in alpha..beta, phi x * k x * v x) ≤ ε * m63ArcLength F c t alpha beta
  rw [← intervalIntegral.integral_sub hhi hki]
  constructor
  · apply intervalIntegral.integral_nonneg_of_forall hab
    intro x
    have hdiff : 0 ≤ h x - k x := sub_nonneg.mpr (curvature_le_regularized F c ε t x)
    have hp : 0 ≤ phi x := (hpsiRange _).1
    have hv0 : 0 ≤ v x := speed_nonneg F c t x
    nlinarith only [mul_nonneg (mul_nonneg hp hdiff) hv0]
  · calc
      _ ≤ ∫ x in alpha..beta, ε * v x := by
        apply intervalIntegral.integral_mono_on hab (hhi.sub hki)
          ((hv.const_mul ε).intervalIntegrable alpha beta)
        intro x _hx
        have hp : 0 ≤ phi x := (hpsiRange _).1
        have hp1 : phi x ≤ 1 := (hpsiRange _).2
        have hv0 : 0 ≤ v x := speed_nonneg F c t x
        calc
          _ = phi x * (h x - k x) * v x := by ring
          _ ≤ phi x * ε * v x := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (regularized_sub_curvature_le F c hε t x) hp) hv0
          _ ≤ ε * v x := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp1 hε) hv0
      _ = _ := intervalIntegral.integral_const_mul _ _




theorem m63ArcCutoff_regularizedIntegral_tendstoUniformlyOn
    (hc : M62ShrinkingCurve F c) {alpha beta : ℝ} (hab : alpha ≤ beta) (x0 r : ℝ)
    (psi : ℝ → ℝ) (hpsi : Continuous psi)
    (hpsiRange : ∀ z, 0 ≤ psi z ∧ psi z ≤ 1)
    {K0 K1 K2 : ℝ} (h2 : 0 ≤ K2)
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    {s T : ℝ} (hs : s ∈ Icc a b) (hT : T ∈ Icc a b) (_hsT : s ≤ T) :
    let Iε : ℝ → ℝ → ℝ := fun ε t => ∫ x in alpha..beta,
      psi (m63ArcLength F c t x0 x / r) *
        m62RegularizedCurvature F c ε t x * curveSpeed F c t x
    let I : ℝ → ℝ := fun t => ∫ x in alpha..beta,
      psi (m63ArcLength F c t x0 x / r) * m62Curvature F c t x * curveSpeed F c t x
    let C := m63ArcLength F c s alpha beta * Real.exp (K2 * (T - s))
    (∀ ε, 0 ≤ ε → ∀ t ∈ Icc s T, 0 ≤ Iε ε t - I t ∧ Iε ε t - I t ≤ ε * C) ∧
      TendstoUniformlyOn Iε I (𝓝[Ici 0] 0) (Icc s T) := by
  dsimp only
  let Iε : ℝ → ℝ → ℝ := fun ε t => ∫ x in alpha..beta,
    psi (m63ArcLength F c t x0 x / r) *
      m62RegularizedCurvature F c ε t x * curveSpeed F c t x
  let I : ℝ → ℝ := fun t => ∫ x in alpha..beta,
    psi (m63ArcLength F c t x0 x / r) * m62Curvature F c t x * curveSpeed F c t x
  let C := m63ArcLength F c s alpha beta * Real.exp (K2 * (T - s))
  change (∀ ε, 0 ≤ ε → ∀ t ∈ Icc s T, 0 ≤ Iε ε t - I t ∧ Iε ε t - I t ≤ ε * C) ∧
    TendstoUniformlyOn Iε I (𝓝[Ici 0] 0) (Icc s T)
  have hL : 0 ≤ m63ArcLength F c s alpha beta :=
    intervalIntegral.integral_nonneg_of_forall hab (speed_nonneg F c s)
  have hbound (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) (ht : t ∈ Icc s T) :
      0 ≤ Iε ε t - I t ∧ Iε ε t - I t ≤ ε * C := by
    have ht' : t ∈ Icc a b := ⟨hs.1.trans ht.1, ht.2.trans hT.2⟩
    have herror := m63ArcCutoff_regularization_error F c hc hab x0 r psi hpsi hpsiRange hε ht'
    have hlength : m63ArcLength F c t alpha beta ≤ C := by
      calc
        _ ≤ m63ArcLength F c s alpha beta * Real.exp (K2 * (t - s)) :=
          m63ArcLength_le_mul_exp F c hc hBounds hab hs ht' ht.1
        _ ≤ C := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 s) h2)) hL
    exact ⟨herror.1, herror.2.trans (mul_le_mul_of_nonneg_left hlength hε)⟩
  refine ⟨hbound, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro δ hδ
  have hlim : Tendsto (fun ε : ℝ => ε * C) (𝓝[Ici 0] 0) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ε * C) := continuous_id.mul continuous_const
    simpa only [zero_mul] using
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[Ici 0] 0, ε * C < δ :=
    hlim.eventually (gt_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin (s := Ici (0 : ℝ)) (a := 0), hsmall] with ε hε hsmall
  intro t ht
  have herr := hbound ε hε t ht
  calc
    dist (I t) (Iε ε t) = Iε ε t - I t := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg herr.1]
    _ ≤ ε * C := herr.2
    _ < δ := hsmall

end PoincareConjecture
