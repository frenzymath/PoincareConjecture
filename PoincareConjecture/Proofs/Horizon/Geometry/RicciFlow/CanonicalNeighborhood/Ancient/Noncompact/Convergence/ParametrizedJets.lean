import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.MovingTimeJets
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.ZeroPullback
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LinearPostcompose
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Bundle Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalParametrizedCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem smooth_zero_convergence_movingTime_euclidean
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    {J : Set ℝ} (hJ : IsCompact J) (hJzero : J ⊆ Iic 0)
    (τ : ℕ → ℝ) (hτ : ∀ k, τ k ∈ J)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin 3) → G.limit.carrier.carrier}
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) :
    let A := fun k y =>
      ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients
        (fun x => ((e k).toFun (0, f x)).2) y -
      (G.limit.flow.flow.metric (τ k)).pullbackCoefficients f y
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let A := fun k y =>
    ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients
      (fun x => ((e k).toFun (0, f x)).2) y -
    (G.limit.flow.flow.metric (τ k)).pullbackCoefficients f y
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := locally_eventually_smooth_movingTime_error
      (e := e) hU hf τ x hx
    exact ⟨W, hW, hxW, hs⟩
  · intro m K hK hKU
    apply (tendstoUniformlyOn_iteratedFDeriv_of_local_convergence (F₀ := fun _ => 0)
      hU ?_ m hK hKU).congr_right
      (fun _ _ => by simp)
    intro x hx
    let q := f x
    let c := extChartAt (𝓡 3) q
    let V := U ∩ f ⁻¹' c.source
    have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU
      (isOpen_extChartAt_source (I := 𝓡 3) q)
    have hxV : x ∈ V := ⟨hx, mem_extChartAt_source q⟩
    let α : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := c ∘ f
    have hα : ContDiffOn ℝ ∞ α V := by
      apply contMDiffOn_iff_contDiffOn.mp
      exact (contMDiffOn_extChartAt (n := ∞) (x := q)).comp (hf.mono inter_subset_left)
        (fun _ hy => by simpa only [c, extChartAt_source] using hy.2)
    have hαV : MapsTo α V c.target := fun y hy => c.map_source hy.2
    obtain ⟨hBlocal, hBjet⟩ := hconv.smooth_zero_convergence_movingTime_chart
      hfixed hJ hJzero τ hτ q
    have hαbound : ∀ L, IsCompact L → L ⊆ V → ∀ r, ∃ C : ℝ,
        ∀ᶠ k : ℕ in atTop, ∀ y ∈ L, ‖iteratedFDeriv ℝ r α y‖ ≤ C := by
      intro L hL hLV r
      obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn
        (fun y hy => ((hα.contDiffAt (hV.mem_nhds (hLV hy))).continuousAt_iteratedFDeriv
          (by exact_mod_cast le_top)).continuousWithinAt)
      exact ⟨C, Eventually.of_forall fun _ => hC⟩
    obtain ⟨_, hDjet⟩ := smooth_zero_convergence_pullback_of_bounded hV hBlocal
      (fun y hy => ⟨V, hV, hy, Eventually.of_forall fun _ => hα⟩) hBjet hαbound
      (fun L hL hLV => ⟨α '' L, hL.image_of_continuousOn (hα.continuousOn.mono hLV),
        image_subset_iff.mpr (hαV.mono_left hLV),
        Eventually.of_forall fun _ => mapsTo_image α L⟩)
    obtain ⟨C, hC, hxC, hCV⟩ := exists_compact_between isCompact_singleton hV
      (singleton_subset_iff.mpr hxV)
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hC.image_of_continuousOn (hf.continuousOn.mono (hCV.trans inter_subset_left)))
    refine ⟨interior C, isOpen_interior, hxC (mem_singleton _),
      interior_subset.trans (hCV.trans inter_subset_left), ?_⟩
    intro r L hL hLC
    apply ((hDjet r L hL (hLC.trans (interior_subset.trans hCV))).congr ?_).congr_right
      (fun _ _ => by simp)
    filter_upwards [eventually_ge_atTop j] with k hjk y hy
    apply (eqOn_iteratedFDeriv_of_isOpen isOpen_interior ?_ r) (hLC hy)
    intro z hz
    have hzV := hCV (interior_subset hz)
    have hfs : f z ∈ G.exhaustion k :=
      G.exhaustion_monotone hjk (hj (mem_image_of_mem f (interior_subset hz)))
    let ψ := fun w => ((e k).toFun (0, c.symm w)).2
    have hcs : c.symm (α z) = f z := c.left_inv hzV.2
    have hψ : MDifferentiableAt (𝓡 3) (𝓡 3) ψ (α z) := by
      have hh := ((e k).contMDiffOn_terminalSpatialMap (t := 0) le_rfl).contMDiffAt
        ((G.exhaustion_open k).mem_nhds hfs)
      rw [← hcs] at hh
      exact (hh.comp _ ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hαV hzV)))).mdifferentiableAt (by simp)
    have hcompose : ψ ∘ α =ᶠ[𝓝 z] (fun w => ((e k).toFun (0, f w)).2) := by
      filter_upwards [hV.mem_nhds hzV] with w hw
      dsimp only [ψ, α, Function.comp_apply]
      rw [c.left_inv hw.2]
    have hcompose₀ : c.symm ∘ α =ᶠ[𝓝 z] f := by
      filter_upwards [hV.mem_nhds hzV] with w hw
      exact c.left_inv hw.2
    have hsource := ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients_comp_of_eventuallyEq
      hψ ((hα.contDiffAt (hV.mem_nhds hzV)).differentiableAt (by simp)) hcompose
    have hlimit := (G.limit.flow.flow.metric (τ k)).pullbackCoefficients_comp_of_eventuallyEq
      (((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target q).mem_nhds (hαV hzV))).mdifferentiableAt (by simp))
      ((hα.contDiffAt (hV.mem_nhds hzV)).differentiableAt (by simp)) hcompose₀
    ext v w
    exact congrArg₂ (fun a b => a - b) (hsource v w) (hlimit v w)

private theorem mfderiv_comp_linearEquiv_apply
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (d : E' ≃L[ℝ] E) (f : E → M) (x v : E') :
    mfderiv 𝓘(ℝ, E') (𝓡 3) (f ∘ d) x v =
      mfderiv 𝓘(ℝ, E) (𝓡 3) f (d x) (d v) := by
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) f (d x)
  · rw [mfderiv_comp x hf d.mdifferentiableAt, ContinuousLinearEquiv.mfderiv_eq]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, E') (𝓡 3) (f ∘ d) x := by
      intro hc
      have hc' : MDifferentiableAt 𝓘(ℝ, E') (𝓡 3) (f ∘ d) (d.symm (d x)) := by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hc
      have hback := hc'.comp (d x) d.symm.mdifferentiableAt
      apply hf
      simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hback
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hf]
    rfl

theorem smooth_zero_convergence_movingTime_parametrized
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    {J : Set ℝ} (hJ : IsCompact J) (hJzero : J ⊆ Iic 0)
    (τ : ℕ → ℝ) (hτ : ∀ k, τ k ∈ J)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    {U : Set E} (hU : IsOpen U) {f : E → G.limit.carrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ f U) :
    let A := fun k y =>
      ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients
        (fun x => ((e k).toFun (0, f x)).2) y -
      (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients f y
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let V := d.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage d.symm.continuous
  have hparam : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ d.symm) V :=
    hf.comp d.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)
  let L : (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] ℝ) := (d.symm.arrowCongr
    (d.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).toContinuousLinearMap
  obtain ⟨hloc, hjet⟩ := hconv.smooth_zero_convergence_movingTime_euclidean
    hfixed hJ hJzero τ hτ hV hparam
  obtain ⟨hLlocal, hLjet⟩ := smooth_convergence_continuousLinearMap_comp
    (G := E →L[ℝ] E →L[ℝ] ℝ) L hV
    (contDiffOn_const (c := (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)))
    hloc (fun m K hK hKV => (hjet m K hK hKV).congr_right (fun _ _ => by simp))
  have hback := compact_jet_convergence_comp_continuousLinearEquiv d hLjet
  have heq {C : FlowCarrier 3} (g : RiemannianMetric 3 C.carrier)
      (F : E → C.carrier) (x : E) :
      L (g.pullbackCoefficients (F ∘ d.symm) (d x)) =
        g.parametrizedCoefficients F x := by
    ext v w
    change g.pullbackCoefficients (F ∘ d.symm) (d x) (d v) (d w) =
      g.parametrizedCoefficients F x v w
    rw [RiemannianMetric.parametrizedCoefficients_apply]
    simp only [RiemannianMetric.pullbackCoefficients, ContinuousLinearMap.bilinearComp_apply]
    erw [mfderiv_comp_linearEquiv_apply, mfderiv_comp_linearEquiv_apply]
    simp only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
    exact congrArg (fun z => g.inner (F z)
      (mfderiv 𝓘(ℝ, E) (𝓡 3) F z v) (mfderiv 𝓘(ℝ, E) (𝓡 3) F z w))
      (d.symm_apply_apply x)
  have hs (k : ℕ) :
      ((L ∘ (fun y => ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients
        (fun z => ((e k).toFun (0, (f ∘ d.symm) z)).2) y -
        (G.limit.flow.flow.metric (τ k)).pullbackCoefficients (f ∘ d.symm) y)) ∘ d) =
      (fun y => ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients
        (fun z => ((e k).toFun (0, f z)).2) y -
        (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients f y) := by
    funext x
    dsimp only [Function.comp_apply]
    have hLsub (a b : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
        L (a - b) = L a - L b := by ext v w; rfl
    rw [hLsub]
    exact congrArg₂ (fun a b => a - b)
      (heq ((S.term (G.subsequence k)).flow.flow.metric (τ k)) (fun z => ((e k).toFun (0, f z)).2) x)
      (heq (G.limit.flow.flow.metric (τ k)) f x)
  have hVback : d ⁻¹' V = U := by ext x; simp [V]
  rw [hVback] at hback
  simp only [hs] at hback
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := locally_eventually_smooth_movingTime_error (e := e) hU hf τ x hx
    exact ⟨W, hW, hxW, hs⟩
  · intro m K hK hKU
    exact (hback m K hK hKU).congr_right (fun _ _ => by simp [Function.comp_def])

end M23TerminalMetricConvergence
end PoincareConjecture
