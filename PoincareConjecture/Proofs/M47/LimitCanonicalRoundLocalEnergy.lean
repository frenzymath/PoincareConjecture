import PoincareConjecture.Proofs.M47.LimitCanonicalRoundSourceTensor
import PoincareConjecture.Proofs.M47.LimitCanonicalRoundIntrinsicJets
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable local instance roundLocalDualGroup : NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance roundLocalDualSpace : NormedSpace ℝ (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance roundLocalBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance roundLocalBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
  [IsManifold (𝓡 3) ∞ X]
  {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private local instance (G : GeneralizedBlowupConvergence V J) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold




noncomputable def limitCanonicalRoundDifferenceTensor
    (G : GeneralizedBlowupConvergence V J) (i : X → G.limit.sliceCarrier.carrier)
    (c : ℝ) (k : ℕ) : CovariantTensorEvaluation 3 X 2 :=
  fun x v => limitCanonicalRoundSourceTensor (G.embedding k) i 0
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ c x v -
      c * (G.limit.flow.metric 0).inner (i x)
        (mfderiv (𝓡 3) (𝓡 3) i x (v 0)) (mfderiv (𝓡 3) (𝓡 3) i x (v 1))




theorem limitCanonical_round_difference_smooth
    (G : GeneralizedBlowupConvergence V J) {i : X → G.limit.sliceCarrier.carrier}
    (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i) (c : ℝ) (k : ℕ)
    (hk : G.exhaustion.space k = univ) :
    IsSmoothCovariantTensor (limitCanonicalRoundDifferenceTensor G i c k) :=
  (limitCanonical_round_source_tensor_smooth (G.embedding k) hk hi 0
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩ c).sub
      ((M44.isSmoothCovariantTensor_metric_pullback (G.limit.flow.metric 0) hi).const_mul c)





theorem limitCanonical_round_local_energy_bound
    (P : M47Predecessors.{u}) (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {i : X → G.limit.sliceCarrier.carrier} (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (c : ℝ) (q : G.limit.sliceCarrier.carrier)
    (g : RiemannianMetric 3 E3) (D : LeviCivitaData g)
    {f : E3 → X} {U K : Set E3} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ a b : E3,
      g.inner y a b = gR.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y a)
        (mfderiv (𝓡 3) (𝓡 3) f y b))
    (hq : MapsTo (i ∘ f) U (extChartAt (𝓡 3) q).source)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      (∑ j ∈ Finset.range (m + 1), gR.tensorNorm
        (DR.iteratedCovariantTensorDerivative
          (limitCanonicalRoundDifferenceTensor G i c k) j) (f x) ^ 2) ≤ eta := by
  have hphi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (i ∘ f) U := hi.comp_contMDiffOn hf
  have hconv := limitCanonical_round_parameter_convergence P G q 0 c
    G.limit.zero_mem hU hphi hq
  obtain ⟨bound, hbound, htail⟩ :=
    limitCanonical_round_intrinsic_difference_bound g D hconv hK hKU m heta
  filter_upwards [htail, limitCanonical_eventually_exhaustion_univ G hcompact] with k hk hfull
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hB := limitCanonical_round_parameter_smooth (G.embedding k) hfull q 0 c hzero
    hU hphi hq
  have hT := limitCanonical_round_difference_smooth G hi c k hfull
  intro x hx
  have hread : ∀ y ∈ U, ∀ v : Fin 2 → E3,
      limitCanonicalRoundParameterField (G.embedding k) q 0 c (i ∘ f) y (v 0) (v 1) -
        (c • (G.limit.flow.metric 0).pullbackCoefficients (i ∘ f) y) (v 0) (v 1) =
      limitCanonicalRoundDifferenceTensor G i c k (f y)
        (fun a => mfderiv (𝓡 3) (𝓡 3) f y (v a)) := by
    intro y hy v
    have hf' := ((hf y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
    have hi' := hi.mdifferentiableAt (x := f y) (by simp)
    rw [limitCanonical_round_source_parameter_readout (G.embedding k) q 0 c hzero
      hi' hf' (hq hy)]
    change _ - c * (G.limit.flow.metric 0).inner _
        (mfderiv (𝓡 3) (𝓡 3) (i ∘ f) y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) (i ∘ f) y (v 1)) = _
    rw [mfderiv_comp y hi' hf']
    rfl
  have heq := limitCanonical_round_local_difference_energy g D gR DR hU hf hinv hmetric
    hB hconv.smooth (limitCanonicalRoundDifferenceTensor G i c k) hT hread m (hKU hx)
  exact (heq ▸ hk x hx).trans hbound.le

end PoincareConjecture.M47
