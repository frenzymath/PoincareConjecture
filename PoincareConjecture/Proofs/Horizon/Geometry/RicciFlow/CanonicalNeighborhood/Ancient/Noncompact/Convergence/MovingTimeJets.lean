import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.BilinearJetConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients

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

local instance movingTimeJetCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

theorem locally_eventually_smooth_movingTime_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → G.limit.carrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ f U) (τ : ℕ → ℝ) :
    ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y =>
        ((S.term (G.subsequence k)).flow.flow.metric (τ k)).parametrizedCoefficients
          (fun z => ((e k).toFun (0, f z)).2) y -
        (G.limit.flow.flow.metric (τ k)).parametrizedCoefficients f y) W := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hx)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn (hf.continuousOn.mono hKU))
  refine ⟨interior K, isOpen_interior, hxK (mem_singleton _), interior_subset.trans hKU, ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk y hy
  have hym := G.exhaustion_monotone hk (hj (mem_image_of_mem f (interior_subset hy)))
  have hfy := hf.contMDiffAt (hU.mem_nhds (hKU (interior_subset hy)))
  have hmap := ((e k).contMDiffOn_terminalSpatialMap (t := 0) le_rfl).contMDiffAt
    ((G.exhaustion_open k).mem_nhds hym) |>.comp y hfy
  exact (((S.term (G.subsequence k)).flow.flow.metric (τ k)).contDiffAt_parametrizedCoefficients
    hmap |>.sub ((G.limit.flow.flow.metric (τ k)).contDiffAt_parametrizedCoefficients hfy)).contDiffWithinAt

theorem smooth_zero_convergence_movingTime_chart
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
      s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
        ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)
    {J : Set ℝ} (hJ : IsCompact J) (hJzero : J ⊆ Iic 0)
    (τ : ℕ → ℝ) (hτ : ∀ k, τ k ∈ J) (q : G.limit.carrier.carrier) :
    let U := (extChartAt (𝓡 3) q).target
    let A := fun k y =>
      ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients
        ((fun x => ((e k).toFun (0, x)).2) ∘ (extChartAt (𝓡 3) q).symm) y -
      (G.limit.flow.flow.metric (τ k)).pullbackCoefficients (extChartAt (𝓡 3) q).symm y
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let c := extChartAt (𝓡 3) q
  let B := fun k => ((S.term (G.subsequence k)).flow.flow.metric (τ k)).pullbackCoefficients
    ((fun x => ((e k).toFun (0, x)).2) ∘ c.symm)
  let B₀ := fun k => (G.limit.flow.flow.metric (τ k)).pullbackCoefficients c.symm
  let A := fun k y => B k y - B₀ k y
  have hlocal : ∀ x ∈ c.target, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hs⟩ := locally_eventually_smooth_movingTime_error
      (e := e) (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm (n := ∞) q) τ x hx
    exact ⟨W, hW, hxW, hs⟩
  refine ⟨hlocal, ?_⟩
  intro m K hK hKU
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKU))
  have hreg : ∀ᶠ k in atTop, ∀ x ∈ K, ContDiffAt ℝ ∞ (A k) x :=
    eventually_contDiffAt_on_compact hK hKU hlocal
  apply (tendstoUniformlyOn_bilinear_jets_of_basis_entries (B := fun _ => 0) hreg
    (fun _ _ => contDiffAt_const) m ?_).congr_right
      (fun _ _ => by simp)
  intro a b
  have hraw := hconv.tendstoUniformlyOn_fixedPullbackSpatialJets hfixed q j m a b
    (hJ.prod hK) (by intro p hp; exact ⟨hJzero hp.1, hKU hp.2, hj (mem_image_of_mem c.symm hp.2)⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hraw η hη,
    eventually_ge_atTop j] with k hk hkj x hx
  have hcx := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target q).mem_nhds (hKU hx))
  have hem := ((e k).contMDiffOn_terminalSpatialMap (t := 0) le_rfl).contMDiffAt
    ((G.exhaustion_open k).mem_nhds
      (G.exhaustion_monotone hkj (hj (mem_image_of_mem c.symm hx))))
  have hBs := (((S.term (G.subsequence k)).flow.flow.metric (τ k)).contDiffAt_pullbackCoefficients
    (hem.comp x hcx) |>.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a)))
      |>.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  have hB₀s := ((G.limit.flow.flow.metric (τ k)).contDiffAt_pullbackCoefficients hcx
    |>.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a)))
      |>.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
  have heq : (fun y => A k y (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b)) =
      (fun y => B k y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) -
      (fun y => B₀ k y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) := rfl
  rw [heq, iteratedFDeriv_sub_apply (hBs.of_le (by exact_mod_cast le_top))
    (hB₀s.of_le (by exact_mod_cast le_top))]
  simp only [zero_apply, iteratedFDeriv_fun_zero, Pi.zero_apply, dist_zero_left]
  rw [norm_sub_rev, ← dist_eq_norm]
  exact hk (τ k, x) ⟨hτ k, hx⟩

end M23TerminalMetricConvergence
end PoincareConjecture
