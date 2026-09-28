import PoincareConjecture.Proofs.M47.LimitCanonicalRoundLocalEnergy
import PoincareConjecture.Proofs.M34.Standard.LocalPullbackRealization
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
  [IsManifold (𝓡 3) ∞ X]
  {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private local instance (G : GeneralizedBlowupConvergence V J) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_round_neighborhood_energy_bound
    (P : M47Predecessors.{u}) (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {i : X → G.limit.sliceCarrier.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (c : ℝ) (m : ℕ) {eta : ℝ} (heta : 0 < eta) (x : X) :
    ∃ W : Set X, W ∈ 𝓝 x ∧ ∀ᶠ k in atTop, ∀ y ∈ W,
      (∑ j ∈ Finset.range (m + 1), gR.tensorNorm
        (DR.iteratedCovariantTensorDerivative
          (limitCanonicalRoundDifferenceTensor G i c k) j) y ^ 2) ≤ eta := by
  let a := extChartAt (𝓡 3) x
  let q := i x
  let U := a.target ∩ a.symm ⁻¹' (i ⁻¹' (extChartAt (𝓡 3) q).source)
  have hU : IsOpen U := (continuousOn_extChartAt_symm x).isOpen_inter_preimage
    (isOpen_extChartAt_target x)
    (hi.continuous.isOpen_preimage _ (isOpen_extChartAt_source q))
  have hxU : a x ∈ U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change i (a.symm (a x)) ∈ (extChartAt (𝓡 3) q).source
    rw [a.left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source q
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm U := by
    intro y hy
    exact (contMDiffWithinAt_extChartAt_symm_target x hy.1).mono inter_subset_left
  have hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) a.symm y).IsInvertible := by
    intro y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) (x := x) hy.1)
  obtain ⟨g, D, U', hU', hxU', hU'U, hmetric⟩ :=
    gR.exists_local_immersive_pullback_realization a.symm hU hxU hf
      (fun y hy => (hinv y hy).injective)
  obtain ⟨K, hK, hxK, hKU'⟩ := exists_compact_subset hU' hxU'
  have hbound := limitCanonical_round_local_energy_bound P G hcompact gR DR hi c q g D
    hU' (hf.mono hU'U) (fun y hy => hinv y (hU'U hy))
    (fun y hy v w => congrArg (fun B : E3 →L[ℝ] E3 →L[ℝ] ℝ => B v w) (hmetric y hy))
    (fun y hy => (hU'U hy).2) hK hKU' m heta
  let W := a.source ∩ a ⁻¹' K
  have hW : W ∈ 𝓝 x := inter_mem (extChartAt_source_mem_nhds x)
    ((continuousAt_extChartAt x).preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hxK))
  refine ⟨W, hW, ?_⟩
  filter_upwards [hbound] with k hk y hy
  simpa only [a.left_inv hy.1] using hk (a y) hy.2

theorem limitCanonical_round_uniform_energy_bound
    [CompactSpace X]
    (P : M47Predecessors.{u}) (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {i : X → G.limit.sliceCarrier.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (c : ℝ) (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ y : X,
      (∑ j ∈ Finset.range (m + 1), gR.tensorNorm
        (DR.iteratedCovariantTensorDerivative
          (limitCanonicalRoundDifferenceTensor G i c k) j) y ^ 2) ≤ eta := by
  classical
  choose W hW hbound using
    limitCanonical_round_neighborhood_energy_bound P G hcompact gR DR hi c m heta
  obtain ⟨S, _hS, hcover⟩ := isCompact_univ.elim_nhds_subcover W (fun x _ => hW x)
  have htail : ∀ᶠ k in atTop, ∀ x ∈ S, ∀ y ∈ W x,
      (∑ j ∈ Finset.range (m + 1), gR.tensorNorm
        (DR.iteratedCovariantTensorDerivative
          (limitCanonicalRoundDifferenceTensor G i c k) j) y ^ 2) ≤ eta :=
    (S.eventually_all).mpr (fun x _ => hbound x)
  filter_upwards [htail] with k hk y
  obtain ⟨x, hx, hy⟩ : ∃ x ∈ S, y ∈ W x := by
    simpa only [mem_iUnion, exists_prop] using hcover (mem_univ y)
  exact hk x hx y hy

end PoincareConjecture.M47
