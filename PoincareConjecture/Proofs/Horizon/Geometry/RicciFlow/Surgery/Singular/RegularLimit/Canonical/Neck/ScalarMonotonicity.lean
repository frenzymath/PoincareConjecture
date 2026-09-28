import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.ReferenceMargin
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit

private theorem endpoint_derivative_margin {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioc a b))
    (hmargin : ∃ᶠ t in 𝓝[<] b, (1 / 2 : ℝ) * f t ^ 2 ≤ derivWithin f (Ioc a b) t) :
    (1 / 2 : ℝ) * f b ^ 2 ≤ derivWithin f (Ioc a b) b := by
  have hfilter : 𝓝[<] b ≤ 𝓝[Ioc a b] b := nhdsWithin_le_of_mem (Ioc_mem_nhdsLT hab)
  have hvalue : Tendsto f (𝓝[<] b) (𝓝 (f b)) :=
    (hf.continuousOn b ⟨hab, le_rfl⟩).mono_left hfilter
  have hderiv : Tendsto (derivWithin f (Ioc a b)) (𝓝[<] b)
      (𝓝 (derivWithin f (Ioc a b) b)) :=
    ((hf.continuousOn_derivWithin (uniqueDiffOn_Ioc a b) (by simp)) b
      ⟨hab, le_rfl⟩).mono_left hfilter
  exact le_of_tendsto_of_tendsto_of_frequently
    (tendsto_const_nhds.mul (hvalue.pow 2)) hderiv hmargin

private theorem exists_strictMonoOn_tail_of_endpoint_derivative_pos
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioc a b))
    (hpos : 0 < derivWithin f (Ioc a b) b) :
    ∃ s : ℝ, a < s ∧ s < b ∧ StrictMonoOn f (Ioc s b) := by
  have hfilter : 𝓝[<] b ≤ 𝓝[Ioc a b] b := nhdsWithin_le_of_mem (Ioc_mem_nhdsLT hab)
  have hderiv : Tendsto (derivWithin f (Ioc a b)) (𝓝[<] b)
      (𝓝 (derivWithin f (Ioc a b) b)) :=
    ((hf.continuousOn_derivWithin (uniqueDiffOn_Ioc a b) (by simp)) b
      ⟨hab, le_rfl⟩).mono_left hfilter
  obtain ⟨c, hcb, hpositive⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (hderiv.eventually_const_lt hpos)
  obtain ⟨s, hs, hsb⟩ := exists_between (max_lt hcb hab)
  have has : a < s := (le_max_right c a).trans_lt hs
  have hcs : c < s := (le_max_left c a).trans_lt hs
  refine ⟨s, has, hsb, strictMonoOn_of_deriv_pos (convex_Ioc s b)
    (hf.continuousOn.mono (Ioc_subset_Ioc_left has.le)) ?_⟩
  intro t ht
  rw [interior_Ioc] at ht
  have h := hpositive ⟨hcs.trans ht.1, ht.2⟩
  change 0 < derivWithin f (Ioc a b) t at h
  rwa [derivWithin_of_mem_nhds (Ioc_mem_nhds (has.trans ht.1) ht.2)] at h



theorem exists_neck_terminal_scalar_monotonicity_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ x : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x →
          (∀ s : ℝ, s < T → ∃ t : ℝ, ∃ ht : t ∈ Ioo H.reference.tMinus T,
            s < t ∧ ∃ N : GeneralizedStrongNeck F t H.epsilon,
              N.center = H.reference.forward t ⟨ht.1.le, ht.2⟩ x) →
          let f := fun t => ((H.terminalFlow P04).connection t).scalarCurvature x
          (1 / 2 : ℝ) * (H.terminalConnection P04).scalarCurvature x ^ 2 ≤
              derivWithin f (Ioc H.reference.tMinus T) T ∧
            ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧ StrictMonoOn f (Ioc s T) := by
  obtain ⟨ε₀, hε₀, hsmall, hmargin⟩ :=
    exists_reference_neck_scalar_time_derivative_margin P04
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε x hR hnecks
  let f := fun t => ((H.terminalFlow P04).connection t).scalarCurvature x
  have hf : ContDiffOn ℝ ∞ f (Ioc H.reference.tMinus T) :=
    ((P04.scalar_regular 3 (H.regularRegion P04) _ (H.terminalFlow P04)).comp
      (contMDiffOn_id.prodMk contMDiffOn_const)
      (fun t ht => ⟨ht, mem_univ x⟩)).contDiffOn
  have hfrequent : ∃ᶠ t in 𝓝[<] T,
      (1 / 2 : ℝ) * f t ^ 2 ≤ derivWithin f (Ioc H.reference.tMinus T) t := by
    apply Filter.frequently_iff.mpr
    intro U hU
    obtain ⟨s, hsT, hs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hU
    obtain ⟨t, ht, hst, N, hcenter⟩ := hnecks s hsT
    obtain ⟨d, hd, hbound⟩ := hmargin H ht N hε x hcenter
    have heq : f =ᶠ[𝓝 t] (fun z => H.reference.scalar z x) := by
      filter_upwards [Iio_mem_nhds ht.2] with z hz
      exact H.terminalFlow_scalar_of_ne P04 hz.ne x
    have hderiv : derivWithin f (Ioc H.reference.tMinus T) t = d :=
      ((hd.congr_of_eventuallyEq heq).hasDerivWithinAt).derivWithin
        (uniqueDiffOn_Ioc _ _ t ⟨ht.1, ht.2.le⟩)
    have hvalue : f t = H.reference.scalar t x := H.terminalFlow_scalar_of_ne P04 ht.2.ne x
    refine ⟨t, hs ⟨hst, ht.2⟩, ?_⟩
    rw [hderiv, hvalue]
    exact hbound
  have hterminal := endpoint_derivative_margin H.reference.tMinus_lt hf hfrequent
  have hvalueT : f T = (H.terminalConnection P04).scalarCurvature x :=
    H.terminalFlow_scalar_at_terminal P04 x
  rw [hvalueT] at hterminal
  have hpos : 0 < derivWithin f (Ioc H.reference.tMinus T) T :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) (sq_pos_of_pos hR)).trans_le hterminal
  exact ⟨hterminal, exists_strictMonoOn_tail_of_endpoint_derivative_pos
    H.reference.tMinus_lt hf hpos⟩

end PoincareConjecture.SingularRegularLimit
