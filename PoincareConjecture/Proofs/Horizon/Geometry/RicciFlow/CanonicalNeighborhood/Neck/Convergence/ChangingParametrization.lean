import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.ZeroPullback
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.ZeroDifference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ParametrizedJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem smooth_zero_convergence_changing_parametrized_coefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → G.limitCarrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ f U)
    {c : ℕ → E → E}
    (hclocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (c k) W)
    (hcbound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (c k) x‖ ≤ C)
    (hctarget : ∀ K, IsCompact K → K ⊆ V → ∃ T,
      IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (c k) K T)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    let A : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun k x =>
      ((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients
        (fun y => ((G.embedding k).toFun (0, f (c k y))).2) x -
      (G.limitFlow.metricAt t).parametrizedCoefficients (f ∘ c k) x
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let F : (k : ℕ) → E → (S.carrier (G.subsequence k)).carrier :=
    fun k y => ((G.embedding k).toFun (0, f y)).2
  let B := fun k => ((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients (F k)
  let B₀ := (G.limitFlow.metricAt t).parametrizedCoefficients f
  let D := fun k y => ((B k (c k y)) - B₀ (c k y)).bilinearComp
    (fderiv ℝ (c k) y) (fderiv ℝ (c k) y)
  let A := fun k x =>
    ((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients (F k ∘ c k) x -
      (G.limitFlow.metricAt t).parametrizedCoefficients (f ∘ c k) x
  obtain ⟨hBlocal, hBjet⟩ := G.smooth_convergence_parametrized_coefficients hzero e hU hf ht
  have hB₀ : ContDiffOn ℝ ∞ B₀ U := fun x hx =>
    ((G.limitFlow.metricAt t).contDiffAt_parametrizedCoefficients
      (hf.contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  obtain ⟨herrorlocal, herrorjet⟩ := smooth_convergence_sub_limit hU hB₀ hBlocal hBjet
  obtain ⟨hDlocal, hDjet⟩ := smooth_zero_convergence_pullback_of_bounded hV
    herrorlocal hclocal herrorjet hcbound hctarget
  have hnear (K : Set E) (hK : IsCompact K) (hKV : K ⊆ V) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ k in atTop, EqOn (D k) (A k) W := by
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
    obtain ⟨T, hT, hTU, hmap⟩ := hctarget K' hK' hK'V
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hT.image_of_continuousOn (hf.continuousOn.mono hTU))
    refine ⟨interior K', isOpen_interior, hKK', ?_⟩
    filter_upwards [hmap, eventually_ge_atTop j,
      eventually_contDiffAt_on_compact hK' hK'V hclocal] with k hkmap hkj hkc x hx
    have hxT := hkmap (interior_subset hx)
    have hfx := hf.contMDiffAt (hU.mem_nhds (hTU hxT))
    have hF : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) (F k) (c k x) :=
      (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero
        (G.exhaustion_monotone hkj (hj (mem_image_of_mem f hxT)))).comp
          (c k x) hfx).mdifferentiableAt (by simp)
    have hc := (hkc x (interior_subset hx)).differentiableAt (by simp)
    change ((B k (c k x)) - B₀ (c k x)).bilinearComp
      (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) = A k x
    have hsub : ((B k (c k x)) - B₀ (c k x)).bilinearComp
        (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) =
        (B k (c k x)).bilinearComp (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) -
        (B₀ (c k x)).bilinearComp (fderiv ℝ (c k) x) (fderiv ℝ (c k) x) := by
      ext v w
      rfl
    rw [hsub]
    exact congrArg₂ (fun v w => v - w)
      (((S.flow (G.subsequence k)).metricAt t).parametrizedCoefficients_comp_of_eventuallyEq
        hF hc Filter.EventuallyEq.rfl)
      ((G.limitFlow.metricAt t).parametrizedCoefficients_comp_of_eventuallyEq
        (hfx.mdifferentiableAt (by simp)) hc Filter.EventuallyEq.rfl)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := hDlocal x hx
    obtain ⟨W', hW', hxW', heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW' (mem_singleton x)⟩, ?_⟩
    filter_upwards [hs, heq] with k hks hkeq
    exact (hks.mono inter_subset_left).congr (fun y hy => (hkeq hy.2).symm)
  · intro m K hK hKV
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKV
    apply (hDjet m K hK hKV).congr
    filter_upwards [heq] with k hk x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hk m) (hKW hx)

end PoincareConjecture.PointedGeometricConvergence
