import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaStrongConvergence
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakClassical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suMixedGrowth_L1_limit {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasure μ]
    {v : ℕ → X → E} {v0 : X → E} {w : ℕ → X → F} {w0 : X → F}
    (hv : ∀ j, MemLp (v j) 4 μ) (hv0 : MemLp v0 4 μ)
    (hw : ∀ j, MemLp (w j) 2 μ) (hw0 : MemLp w0 2 μ)
    (hvlim : Tendsto (fun j => eLpNorm (v j - v0) 4 μ) atTop (𝓝 0))
    (hwlim : Tendsto (fun j => eLpNorm (w j - w0) 2 μ) atTop (𝓝 0))
    (A : X → E × F → ℝ)
    (hAc : ∀ᵐ x ∂μ, ContinuousAt (A x) (v0 x, w0 x))
    (hA : ∀ j, AEStronglyMeasurable (fun x => A x (v j x, w j x)) μ)
    (hA0 : AEStronglyMeasurable (fun x => A x (v0 x, w0 x)) μ)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ j, ∀ᵐ x ∂μ,
      ‖A x (v j x, w j x)‖ ≤ C * (1 + ‖v j x‖ ^ 4 + ‖w j x‖ ^ 2))
    (hbound0 : ∀ᵐ x ∂μ,
      ‖A x (v0 x, w0 x)‖ ≤ C * (1 + ‖v0 x‖ ^ 4 + ‖w0 x‖ ^ 2)) :
    (∀ j, Integrable (fun x => A x (v j x, w j x)) μ) ∧
    Integrable (fun x => A x (v0 x, w0 x)) μ ∧
    Tendsto (fun j => eLpNorm
      (fun x => A x (v j x, w j x) - A x (v0 x, w0 x)) 1 μ) atTop (𝓝 0) := by
  have hvpow (j) : MemLp (fun x => ‖v j x‖ ^ 4) 1 μ := by
    simpa using (hv j).norm_rpow (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hwpow (j) : MemLp (fun x => ‖w j x‖ ^ 2) 1 μ := by
    simpa using (hw j).norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hv0pow : MemLp (fun x => ‖v0 x‖ ^ 4) 1 μ := by
    simpa using hv0.norm_rpow (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hw0pow : MemLp (fun x => ‖w0 x‖ ^ 2) 1 μ := by
    simpa using hw0.norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hUIv : UnifIntegrable (fun j x => ‖v j x‖ ^ 4) 1 μ := by
    have hvUI : UnifIntegrable v 4 μ :=
      unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hv hv0 hvlim
    simpa using suAlpha_power_uniformIntegrable (by norm_num : (0 : ℝ) < 4)
      (by simpa using hvUI)
  have hUIw : UnifIntegrable (fun j x => ‖w j x‖ ^ 2) 1 μ := by
    have hwUI : UnifIntegrable w 2 μ :=
      unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num) hw hw0 hwlim
    simpa using suAlpha_power_uniformIntegrable (by norm_num : (0 : ℝ) < 2)
      (by simpa using hwUI)
  have hbase : UnifIntegrable (fun j x => 1 + ‖v j x‖ ^ 4 + ‖w j x‖ ^ 2) 1 μ :=
    ((unifIntegrable_const (by rfl) ENNReal.one_ne_top (memLp_const (1 : ℝ))).add
      hUIv (by rfl) (fun _ => aestronglyMeasurable_const) (fun j => (hvpow j).1)).add
      hUIw (by rfl) (fun j => aestronglyMeasurable_const.add (hvpow j).1)
        (fun j => (hwpow j).1)
  have hUI : UnifIntegrable (fun j x => A x (v j x, w j x)) 1 μ :=
    suAlpha_uniformIntegrable_dominated hC hbase (fun j => by
      filter_upwards [hbound j] with x hx
      simpa only [Real.norm_of_nonneg (by positivity :
        0 ≤ 1 + ‖v j x‖ ^ 4 + ‖w j x‖ ^ 2)] using hx)
  have hlimLp : MemLp (fun x => A x (v0 x, w0 x)) 1 μ :=
    (((memLp_const (1 : ℝ)).add hv0pow).add hw0pow).const_mul C |>.of_le hA0 (by
      filter_upwards [hbound0] with x hx
      simpa only [Pi.add_apply, Real.norm_of_nonneg (by positivity :
        0 ≤ C * (1 + ‖v0 x‖ ^ 4 + ‖w0 x‖ ^ 2))] using hx)
  refine ⟨fun j => ?_, memLp_one_iff_integrable.mp hlimLp, ?_⟩
  · exact memLp_one_iff_integrable.mp
      ((((memLp_const (1 : ℝ)).add (hvpow j)).add (hwpow j)).const_mul C |>.of_le (hA j) (by
        filter_upwards [hbound j] with x hx
        simpa only [Pi.add_apply, Real.norm_of_nonneg (by positivity :
          0 ≤ C * (1 + ‖v j x‖ ^ 4 + ‖w j x‖ ^ 2))] using hx))
  · apply tendsto_of_subseq_tendsto
    intro ns hns
    have hvm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (fun j => (hv (ns j)).1) hv0.1 (hvlim.comp hns)
    obtain ⟨ms, hms, hvpoint⟩ := hvm.exists_seq_tendsto_ae
    have hwm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun j => (hw (ns (ms j))).1) hw0.1 (hwlim.comp (hns.comp hms.tendsto_atTop))
    obtain ⟨ks, hks, hwpoint⟩ := hwm.exists_seq_tendsto_ae
    have hpoint : ∀ᵐ x ∂μ, Tendsto
        (fun j => A x (v (ns (ms (ks j))) x, w (ns (ms (ks j))) x))
        atTop (𝓝 (A x (v0 x, w0 x))) := by
      filter_upwards [hvpoint, hwpoint, hAc] with x hvx hwx hcx
      exact hcx.tendsto.comp ((hvx.comp hks.tendsto_atTop).prodMk_nhds hwx)
    have hUI' : UnifIntegrable (fun j x => A x (v (ns (ms (ks j))) x,
        w (ns (ms (ks j))) x)) 1 μ := by
      intro eps heps
      obtain ⟨d, hd, hh⟩ := hUI heps
      exact ⟨d, hd, fun j => hh (ns (ms (ks j)))⟩
    exact ⟨ms ∘ ks, tendsto_Lp_finite_of_tendsto_ae (by rfl) ENNReal.one_ne_top
      (fun j => hA (ns (ms (ks j)))) hlimLp hUI' hpoint⟩

private theorem test_pairing_tendsto {μ : Measure Plane} {φ u : Plane → ℝ}
    {v : ℕ → Plane → ℝ} (hφ : MemLp φ ⊤ μ)
    (hu : MemLp u 1 μ) (hv : ∀ j, MemLp (v j) 1 μ)
    (hlim : Tendsto (fun j => eLpNorm (v j - u) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, v j x * φ x ∂μ) atTop (𝓝 (∫ x, u x * φ x ∂μ)) := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  have heq (a : Plane → ℝ) (ha : MemLp a 1 μ) :
      B.lpPairing μ ⊤ 1 (hφ.toLp φ) (ha.toLp a) = ∫ x, a x * φ x ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp, ha.coeFn_toLp] with x hx hy
    simp [B, hx, hy, mul_comm]
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).mpr hlim
  have h := (B.lpPairing μ ⊤ 1 (hφ.toLp φ)).continuous.tendsto (hu.toLp u)
  simpa only [Function.comp_def, heq] using h.comp ht

theorem suWeakPartial_of_L1_approx {O : Set Plane} {i : Fin 2}
    {u p : Plane → ℝ} {v q : ℕ → Plane → ℝ}
    (hu : IntegrableOn u O) (hp : IntegrableOn p O)
    (hv : ∀ j, IntegrableOn (v j) O) (hq : ∀ j, IntegrableOn (q j) O)
    (hw : ∀ j, HasWeakPartialDeriv i (q j) (v j) O)
    (hvlim : Tendsto (fun j => eLpNorm (v j - u) 1 (volume.restrict O)) atTop (𝓝 0))
    (hqlim : Tendsto (fun j => eLpNorm (q j - p) 1 (volume.restrict O)) atTop (𝓝 0)) :
    HasWeakPartialDeriv i p u O := by
  intro φ hφ hc hs
  have hφLp : MemLp φ ⊤ (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hdφLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) ⊤
      (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) _)).restrict O
  have hl := test_pairing_tendsto hdφLp (memLp_one_iff_integrable.mpr hu)
    (fun j => memLp_one_iff_integrable.mpr (hv j)) hvlim
  have hr := (test_pairing_tendsto hφLp (memLp_one_iff_integrable.mpr hp)
    (fun j => memLp_one_iff_integrable.mpr (hq j)) hqlim).neg
  exact tendsto_nhds_unique hl (hr.congr (fun j => (hw j φ hφ hc hs).symm))

end PoincareConjecture.M60

end
