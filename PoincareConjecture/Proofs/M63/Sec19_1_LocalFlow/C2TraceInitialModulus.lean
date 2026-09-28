import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceCurvatureForcing
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicGaussianRestartBound
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicGaussianUniformTrace
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import Mathlib.Analysis.SpecificLimits.Basic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)





theorem exists_uniform_embeddedCurvature_heat_error
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    ∃ D E : ℝ, (0 ≤ D ∧ 0 ≤ E) ∧
      ∀ (c : ℝ → ℝ → M) (_hc : M62ShrinkingCurve F c) (v0 : ℝ), v0 ∈ Icc m0 V0 →
      (∀ x, curveSpeed F c a x = v0) →
      (∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R) →
      (∀ t ∈ Ioo a b, ∀ x,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
          J / Real.sqrt (t - a)) →
      ∀ h : ℝ → X,
      (∀ t ∈ Icc a b, ∀ x : ℝ, h t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)) →
      ∀ t ∈ Icc a b,
        ‖h t - periodicGaussianHeat ((v0 ^ 2)⁻¹ * (t - a)) (h a)‖ ≤
          D * (t - a) + E * Real.sqrt (t - a) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  obtain ⟨A, B, C, ⟨hA, hB, hC⟩, hforcing⟩ :=
    exists_uniform_embeddedCurvature_forcing_bounds F hab hcompact he hK hR hJ
      hBounds hm0 hmV
  let K1 := ∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖
  let D := K1 * V0 * A + B
  let E := 2 * C
  have hK1 : 0 ≤ K1 := integral_nonneg fun _ => norm_nonneg _
  have hV0 : 0 < V0 := hm0.trans_le hmV
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨D, E, ⟨hD, hE⟩, ?_⟩
  intro c hc v0 hv0 hInitial hCurv hJet h hrep
  let H : ℝ → ℝ → W := fun t x =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
  let ν := (v0 ^ 2)⁻¹
  let η : ℝ → ℝ → ℝ := fun t x => (curveSpeed F c t x ^ 2)⁻¹ - ν
  have hv0pos : 0 < v0 := hm0.trans_le hv0.1
  have hν : 0 < ν := inv_pos.mpr (sq_pos_of_pos hv0pos)
  have hforce := hforcing c hc v0 hv0 hInitial hCurv hJet
  obtain ⟨h₀, h₁, h₂, hdot, hh₀, hh₁, hh₂, hhdot,
    hval₀, hval₁, hval₂, hvaldot, hx, hxx, htime⟩ :=
    exists_periodic_embeddedCurvature_restart_data F c hab hc he
  have hsame (t : ℝ) (ht : t ∈ Icc a b) : h t = h₀ t := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (hrep t ht x).trans (hval₀ t ht x).symm
  have hh : ContinuousOn h (Icc a b) := hh₀.congr hsame
  have hηsmooth (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ 1 (η t) :=
    (((M62.speed_contDiff F c hc (Ioo_subset_Icc_self ht)).pow 2).inv
      (fun x => pow_ne_zero 2 (M62.speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne')).sub
        contDiff_const
  have hηper (t : ℝ) (ht : t ∈ Ioo a b) : Function.Periodic (η t) curvePeriod := by
    intro x
    dsimp only [η]
    rw [M62.speed_periodic F c hc (Ioo_subset_Icc_self ht) x]
  have hη₁per (t : ℝ) (ht : t ∈ Ioo a b) :
      Function.Periodic (deriv (η t)) curvePeriod :=
    (hηper t ht).deriv_of_differentiable ((hηsmooth t ht).differentiable (by norm_num))
  let ηc : ℝ → C(AddCircle curvePeriod, ℝ) := fun t =>
    if ht : t ∈ Ioo a b then
      ⟨(hηper t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
          (hηsmooth t ht).continuous⟩
    else 0
  let η₁c : ℝ → C(AddCircle curvePeriod, ℝ) := fun t =>
    if ht : t ∈ Ioo a b then
      ⟨(hη₁per t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
          (hηsmooth t ht).continuous_deriv_one⟩
    else 0
  have hηc (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      ηc t (x : AddCircle curvePeriod) = η t x := by
    simp only [ηc, dif_pos ht]
    rfl
  have hη₁c (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      η₁c t (x : AddCircle curvePeriod) = deriv (η t) x := by
    simp only [η₁c, dif_pos ht]
    rfl
  let F₀ : ℝ → X := fun t => ηc t • h₁ t
  let F₁ : ℝ → X := fun t => η₁c t • h₁ t + ηc t • h₂ t
  let G : ℝ → X := fun t =>
    (hdot t - (ηc t + ContinuousMap.const _ ν) • h₂ t) - η₁c t • h₁ t
  have hF₀val (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      F₀ t (x : AddCircle curvePeriod) = η t x • deriv (H t) x := by
    change ηc t (x : AddCircle curvePeriod) • h₁ t (x : AddCircle curvePeriod) = _
    rw [hηc t ht x, hval₁ t ht x]
  have hF₁val (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      F₁ t (x : AddCircle curvePeriod) =
        deriv (η t) x • deriv (H t) x + η t x • iteratedDeriv 2 (H t) x := by
    change η₁c t (x : AddCircle curvePeriod) • h₁ t (x : AddCircle curvePeriod) +
      ηc t (x : AddCircle curvePeriod) • h₂ t (x : AddCircle curvePeriod) = _
    rw [hη₁c t ht x, hηc t ht x, hval₁ t ht x, hval₂ t ht x]
  have hGval (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      G t (x : AddCircle curvePeriod) =
        (deriv (fun r => H r x) t - (curveSpeed F c t x ^ 2)⁻¹ • iteratedDeriv 2 (H t) x) -
          deriv (η t) x • deriv (H t) x := by
    change (hdot t (x : AddCircle curvePeriod) -
      (ηc t (x : AddCircle curvePeriod) + ν) • h₂ t (x : AddCircle curvePeriod)) -
        η₁c t (x : AddCircle curvePeriod) • h₁ t (x : AddCircle curvePeriod) = _
    rw [hvaldot t ht x, hηc t ht x, hval₂ t ht x, hη₁c t ht x, hval₁ t ht x]
    simp only [η, sub_add_cancel]
    rfl
  have hFderiv (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun y : ℝ => F₀ t (y : AddCircle curvePeriod))
        (F₁ t (x : AddCircle curvePeriod)) x := by
    rw [show (fun y : ℝ => F₀ t (y : AddCircle curvePeriod)) =
      (fun y => η t y • deriv (H t) y) from funext (hF₀val t ht), hF₁val t ht x]
    exact (hforce t ht x).1
  have hresidual (t : ℝ) (ht : t ∈ Ioo a b) : hdot t - ν • h₂ t = F₁ t + G t := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change hdot t (x : AddCircle curvePeriod) - ν • h₂ t (x : AddCircle curvePeriod) =
      F₁ t (x : AddCircle curvePeriod) + G t (x : AddCircle curvePeriod)
    rw [hvaldot t ht x, hval₂ t ht x, hF₁val t ht x, hGval t ht x]
    exact (hforce t ht x).2.1
  have hFnorm (t : ℝ) (ht : t ∈ Ioo a b) : ‖F₀ t‖ ≤ A * Real.sqrt (t - a) := by
    apply (ContinuousMap.norm_le (F₀ t) (mul_nonneg hA (Real.sqrt_nonneg _))).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hF₀val t ht x]
    exact (hforce t ht x).2.2.1
  have hGnorm (t : ℝ) (ht : t ∈ Ioo a b) : ‖G t‖ ≤ B + C / Real.sqrt (t - a) := by
    apply (ContinuousMap.norm_le (G t)
      (add_nonneg hB (div_nonneg hC (Real.sqrt_nonneg _)))).mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hGval t ht x]
    exact (hforce t ht x).2.2.2
  have hsqrt : Real.sqrt ν = v0⁻¹ := by
    dsimp only [ν]
    rw [Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hv0pos]
  have hcoef : 2 * (K1 / (2 * Real.sqrt ν)) * A + B ≤ D := by
    calc
      _ = K1 * v0 * A + B := by
        rw [hsqrt]
        field_simp
      _ ≤ D := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv0.2 hK1) hA) le_rfl
  have hrestart (τ σ : ℝ) (hτ : 0 < τ) (hτb : τ < b - a)
      (hσ : 0 < σ) (hστ : σ ≤ τ) :
      ‖h₀ (a + τ) - periodicGaussianHeat (ν * (τ - σ)) (h₀ (a + σ))‖ ≤
        D * τ + E * Real.sqrt τ := by
    have hmap (r : ℝ) (hr : r ∈ Icc σ τ) : a + r ∈ Ioo a b := by
      constructor <;> linarith [hr.1, hr.2]
    have hc₀ : ContinuousOn (fun r => h₀ (a + r)) (Icc σ τ) :=
      hh₀.comp (continuous_const.add continuous_id).continuousOn
        (fun r hr => Ioo_subset_Icc_self (hmap r hr))
    have hc₁ : ContinuousOn (fun r => h₁ (a + r)) (Icc σ τ) :=
      hh₁.comp (continuous_const.add continuous_id).continuousOn hmap
    have hc₂ : ContinuousOn (fun r => h₂ (a + r)) (Icc σ τ) :=
      hh₂.comp (continuous_const.add continuous_id).continuousOn hmap
    have hct : ContinuousOn (fun r => hdot (a + r)) (Icc σ τ) :=
      hhdot.comp (continuous_const.add continuous_id).continuousOn hmap
    have htd (r : ℝ) (hr : r ∈ Ioo σ τ) (x : ℝ) :
        HasDerivAt (fun s => h₀ (a + s) (x : AddCircle curvePeriod))
          (hdot (a + r) (x : AddCircle curvePeriod)) r := by
      simpa only [Function.comp_def, one_smul] using
        (htime (a + r) (hmap r (Ioo_subset_Icc_self hr)) x).scomp r
          ((hasDerivAt_id r).const_add a)
    have hbound := periodicGaussianHeat_restart_norm_bound hσ hστ hν hA hB hC
      (fun r => h₀ (a + r)) (fun r => h₁ (a + r)) (fun r => h₂ (a + r))
      (fun r => hdot (a + r)) (fun r => F₀ (a + r)) (fun r => F₁ (a + r))
      (fun r => G (a + r)) hc₀ hc₁ hc₂ hct
      (fun r hr => hx (a + r) (hmap r hr))
      (fun r hr => hxx (a + r) (hmap r hr)) htd
      (fun r hr => hFderiv (a + r) (hmap r (Ioo_subset_Icc_self hr)))
      (fun r hr => hresidual (a + r) (hmap r (Ioo_subset_Icc_self hr)))
      (fun r hr => by
        simpa only [add_sub_cancel_left] using
          hFnorm (a + r) (hmap r (Ioo_subset_Icc_self hr)))
      (fun r hr => by
        simpa only [add_sub_cancel_left] using
          hGnorm (a + r) (hmap r (Ioo_subset_Icc_self hr)))
    exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef hτ.le) le_rfl)
  have hinitial (τ : ℝ) (hτ : 0 < τ) (hτb : τ < b - a) :
      ‖h₀ (a + τ) - periodicGaussianHeat (ν * τ) (h₀ a)‖ ≤
        D * τ + E * Real.sqrt τ := by
    let σ : ℕ → ℝ := fun k => τ * (1 / ((k : ℝ) + 1))
    have hσpos (k : ℕ) : 0 < σ k := by dsimp only [σ]; positivity
    have hστ (k : ℕ) : σ k ≤ τ := by
      dsimp only [σ]
      apply mul_le_of_le_one_right hτ.le
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hσzero : Tendsto σ atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul τ
    have hatime : Tendsto (fun k => a + σ k) atTop (𝓝[Icc a b] a) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa only [add_zero] using hσzero.const_add a
      · exact ⟨by linarith [hσpos k], by linarith [hστ k]⟩
    have hpath : Tendsto (fun k => h₀ (a + σ k)) atTop (𝓝 (h₀ a)) :=
      (hh₀ a ⟨le_rfl, hab.le⟩).tendsto.comp hatime
    have hlag : Tendsto (fun k => ν * (τ - σ k)) atTop (𝓝 (ν * τ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hσzero).const_mul ν
    have hheat := continuous_periodicGaussianHeat_action.continuousAt.tendsto.comp
      (hlag.prodMk_nhds hpath)
    exact le_of_tendsto' (tendsto_const_nhds.sub hheat).norm
      (fun k => hrestart τ (σ k) hτ hτb (hσpos k) (hστ k))
  have hinterior (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖h t - periodicGaussianHeat (ν * (t - a)) (h a)‖ ≤
        D * (t - a) + E * Real.sqrt (t - a) := by
    rw [hsame t (Ioo_subset_Icc_self ht), hsame a ⟨le_rfl, hab.le⟩]
    simpa only [add_sub_cancel] using
      hinitial (t - a) (sub_pos.mpr ht.1) (sub_lt_sub_right ht.2 a)
  have hleft : ContinuousOn (fun t =>
      ‖h t - periodicGaussianHeat (ν * (t - a)) (h a)‖) (Icc a b) :=
    (hh.sub (continuous_periodicGaussianHeat_action.comp_continuousOn
      (((continuous_const.mul (continuous_id.sub continuous_const)).prodMk
        continuous_const).continuousOn))).norm
  have hright : Continuous (fun t : ℝ => D * (t - a) + E * Real.sqrt (t - a)) :=
    (continuous_const.mul (continuous_id.sub continuous_const)).add
      (continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.sub continuous_const)))
  intro t ht
  exact le_on_closure hinterior (by simpa only [closure_Ioo hab.ne] using hleft)
    hright.continuousOn (by simpa only [closure_Ioo hab.ne] using ht)




theorem embeddedCurvature_uniform_initial_trace_on_compact_data
    (F : RicciFlow n M (Icc a b)) (hab : a < b)
    (hcompact : IsCompact (univ : Set M)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {K R J m0 V0 : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J)
    (hBounds : CurveEvolutionAmbientBounds F K K K) (hm0 : 0 < m0) (hmV : m0 ≤ V0)
    {Kinitial : Set X} (hinitial : IsCompact Kinitial) {ε : ℝ} (hε : 0 < ε) :
    let _ : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
    ∃ d : ℝ, 0 < d ∧
      ∀ (c : ℝ → ℝ → M) (_hc : M62ShrinkingCurve F c) (v0 : ℝ), v0 ∈ Icc m0 V0 →
      (∀ x, curveSpeed F c a x = v0) →
      (∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R) →
      (∀ t ∈ Ioo a b, ∀ x,
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
          J / Real.sqrt (t - a)) →
      ∀ h : ℝ → X,
      (∀ t ∈ Icc a b, ∀ x : ℝ, h t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)) →
      h a ∈ Kinitial → ∀ t ∈ Icc a b, t - a < d → ‖h t - h a‖ < ε := by
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  obtain ⟨D, E, _, herror⟩ := exists_uniform_embeddedCurvature_heat_error
    F hab hcompact he hK hR hJ hBounds hm0 hmV
  have hcerror : Continuous (fun τ : ℝ => D * τ + E * Real.sqrt τ) :=
    (continuous_const.mul continuous_id).add (continuous_const.mul Real.continuous_sqrt)
  have hzero : D * (0 : ℝ) + E * Real.sqrt 0 < ε / 2 := by
    simpa only [mul_zero, Real.sqrt_zero, add_zero] using half_pos hε
  obtain ⟨dError, hdError, hnear⟩ := Metric.mem_nhds_iff.mp
    (hcerror.continuousAt.eventually (isOpen_Iio.mem_nhds hzero))
  obtain ⟨dHeat, hdHeat, hheat⟩ :=
    periodicGaussianHeat_uniform_initial_trace hinitial (half_pos hε)
  let d := min dError (dHeat * m0 ^ 2)
  have hd : 0 < d := lt_min hdError (mul_pos hdHeat (sq_pos_of_pos hm0))
  refine ⟨d, hd, ?_⟩
  intro c hc v0 hv0 hInitial hCurv hJet h hrep hKinitial t ht htd
  have hτ : 0 ≤ t - a := sub_nonneg.mpr ht.1
  have hv0pos : 0 < v0 := hm0.trans_le hv0.1
  have herr : D * (t - a) + E * Real.sqrt (t - a) < ε / 2 :=
    hnear (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hτ]
      exact htd.trans_le (min_le_left _ _))
  have hsq : m0 ^ 2 ≤ v0 ^ 2 := by nlinarith [hv0.1]
  have hlag : |(v0 ^ 2)⁻¹ * (t - a)| < dHeat := by
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) hτ)]
    calc
      (v0 ^ 2)⁻¹ * (t - a) = (t - a) / v0 ^ 2 := by ring
      _ ≤ (t - a) / m0 ^ 2 := div_le_div_of_nonneg_left hτ (sq_pos_of_pos hm0) hsq
      _ < dHeat := (div_lt_iff₀ (sq_pos_of_pos hm0)).mpr
        (htd.trans_le (min_le_right _ _))
  have hheaterr := hheat ((v0 ^ 2)⁻¹ * (t - a)) hlag (h a) hKinitial
  have herrbound := herror c hc v0 hv0 hInitial hCurv hJet h hrep t ht
  have htriangle := norm_add_le
    (h t - periodicGaussianHeat ((v0 ^ 2)⁻¹ * (t - a)) (h a))
    (periodicGaussianHeat ((v0 ^ 2)⁻¹ * (t - a)) (h a) - h a)
  rw [sub_add_sub_cancel] at htriangle
  exact htriangle.trans_lt (by linarith)

end PoincareConjecture.M63
