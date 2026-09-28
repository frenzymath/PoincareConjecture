import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Coefficients

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

open Poincare.Analysis.Calculus

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "T" => E →L[ℝ] E →L[ℝ] ℝ

def normalizedPotentialForcing (z : L.limitCarrier.carrier) (k : ℕ) (x : E) : T :=
  (2 * S.potentialGradientScale (q (L.subsequence k)))⁻¹ •
    (G.normalizedPotentialSpacetimeCoefficients L z k (0, x) +
      fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x) (1, 0))

theorem normalizedPotentialCoefficients_timeDerivative_bounds
    (z : L.limitCarrier.carrier) :
    LocallyEventuallyContDiff (extChartAt (𝓡 3) z).target
      (fun k x => fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x) (1, 0)) ∧
    LocallyEventuallyBoundedDerivatives (extChartAt (𝓡 3) z).target
      (fun k x => fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x) (1, 0)) := by
  let Ω := (extChartAt (𝓡 3) z).target
  let U := Ioo (-1 : ℝ) (1 / 2) ×ˢ Ω
  let H₀ : ℝ × E → T := fun p =>
    (L.limitFlow.metric p.1).pullbackCoefficients (extChartAt (𝓡 3) z).symm p.2
  have hU : IsOpen U := isOpen_Ioo.prod (isOpen_extChartAt_target z)
  have hs : ContDiffOn ℝ ∞ H₀ U := by
    intro p hp
    exact (L.limitFlow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Iio
      ((contMDiffOn_extChartAt_symm (n := ∞) z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hp.2))
      (hp.1.2.trans (by norm_num))).contDiffWithinAt
  have hlocal : ∀ p ∈ U, ∃ V, IsOpen V ∧ p ∈ V ∧ ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k)) V := by
    intro p hp
    obtain ⟨V, hV, hpV, hk⟩ := G.normalizedPotentialSpacetimeCoefficients_locally_smooth L z p hp
    exact ⟨V, hV, hpV, hk.mono fun _ h => h.fderiv_of_isOpen hV (by simp)⟩
  obtain ⟨hlocal', hjet⟩ := smooth_convergence_comp_continuousLinearMap
    (ContinuousLinearMap.inr ℝ ℝ E) hU (hs.fderiv_of_isOpen hU (by simp)) hlocal
    (fun r K hK hKU => tendstoUniformlyOn_fderiv_jets r
      (G.normalizedPotentialSpacetimeCoefficients_tendsto_jets L z (r + 1) hK hKU))
  have hpre : (ContinuousLinearMap.inr ℝ ℝ E) ⁻¹' U = Ω := by ext x; simp [U]
  rw [hpre] at hlocal' hjet
  have hds : LocallyEventuallyContDiff Ω
      (fun k x => fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x)) :=
    locallyEventuallyContDiff_of_local hlocal'
  have hd₀ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ H₀ (0, x)) Ω := by
    simpa only [hpre, Function.comp_def, ContinuousLinearMap.inr_apply] using
      (hs.fderiv_of_isOpen hU (by simp)).comp_continuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)
  have hdb : LocallyEventuallyBoundedDerivatives Ω
      (fun k x => fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x)) :=
    locallyEventuallyBoundedDerivatives_of_tendsto_jets (isOpen_extChartAt_target z) hd₀ hjet
  let ev : ((ℝ × E) →L[ℝ] T) →L[ℝ] T := ContinuousLinearMap.apply ℝ T (1, 0)
  exact ⟨hds.clm ev, hdb.clm hds ev⟩

theorem normalizedPotentialForcing_bounds
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (z : L.limitCarrier.carrier) :
    LocallyEventuallyContDiff (extChartAt (𝓡 3) z).target
      (G.normalizedPotentialForcing L z) ∧
    LocallyEventuallyBoundedDerivatives (extChartAt (𝓡 3) z).target
      (G.normalizedPotentialForcing L z) := by
  let Ω := (extChartAt (𝓡 3) z).target
  let P : ℕ → E → T := fun k x => G.normalizedPotentialSpacetimeCoefficients L z k (0, x)
  let Q : ℕ → E → T := fun k x =>
    fderiv ℝ (G.normalizedPotentialSpacetimeCoefficients L z k) (0, x) (1, 0)
  obtain ⟨hPs, hPjet⟩ := G.normalizedPotentialCoefficients_smooth_convergence L z
  have hPb := locallyEventuallyBoundedDerivatives_of_tendsto_jets
    (isOpen_extChartAt_target z) ((L.limitFlow.metric 0).contDiffOn_chartCoefficients z) hPjet
  obtain ⟨hQs, hQb⟩ := G.normalizedPotentialCoefficients_timeDerivative_bounds L z
  let addL : T × T →L[ℝ] T := ContinuousLinearMap.fst ℝ T T + ContinuousLinearMap.snd ℝ T T
  have hab := (hPb.prodMk hQb hPs hQs).clm (hPs.prodMk hQs) addL
  have has := (hPs.prodMk hQs).clm addL
  have hscale := G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape
  constructor
  · intro K hK hKΩ
    filter_upwards [has K hK hKΩ] with k ⟨V, hV, hKV, hks⟩
    exact ⟨V, hV, hKV, hks.const_smul _⟩
  · intro K hK hKΩ m
    obtain ⟨B, hB⟩ := hab K hK hKΩ m
    refine ⟨|B|, ?_⟩
    filter_upwards [hB, has K hK hKΩ, hscale.eventually_gt_atTop 1]
      with k hkB ⟨V, hV, hKV, hks⟩ hk x hx
    change ContDiffOn ℝ ∞ (fun x => addL (P k x, Q k x)) V at hks
    change ‖iteratedFDeriv ℝ m
      ((2 * S.potentialGradientScale (q (L.subsequence k)))⁻¹ •
        fun y => addL (P k y, Q k y)) x‖ ≤ |B|
    rw [iteratedFDeriv_const_smul_apply
      ((hks.contDiffAt (hV.mem_nhds (hKV hx))).of_le
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)), norm_smul]
    have hnorm : ‖(2 * S.potentialGradientScale (q (L.subsequence k)))⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
      exact (inv_le_one₀ (by linarith)).mpr (by linarith)
    exact (mul_le_mul hnorm ((hkB x hx).trans (le_abs_self B)) (norm_nonneg _)
      zero_le_one).trans_eq (one_mul _)

end PoincareConjecture.ShrinkingSolitonFlow
