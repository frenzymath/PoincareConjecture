import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.GradientTimeContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.SlabHessian
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MovingL2Chain
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.CompletedEntropy









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2V" => Lp V 2 (volume : Measure V)

theorem metricEntropy_field_time_chain {J : Set ℝ} (F : RicciFlow n V J)
    {a b t : ℝ} (hJ : Icc a b ⊆ J) (ht : t ∈ Ioo a b)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {Q : ℝ} (hQ : 0 ≤ Q) (U : ℝ → L2V) {v : L2V} (hU : HasDerivAt U v t) :
    HasDerivAt (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) (U s))
      (fieldIntegral (metricEntropyTimePotential (F.connection t) η Q) (U t) +
        inner ℝ (metricEntropyGradientLp (F.metric t) hη hc Q (U t)) v) t := by
  obtain ⟨C, _, hR⟩ := metricEntropyPotential_slab_remainder F isCompact_Icc hJ
    hη.continuous hc hQ
  apply moving_hilbert_entropy_hasDerivAt
    (fun s u => fieldIntegral (metricEntropyPotential (F.metric s) η Q) u) U
    (fun s => metricEntropyGradientLp (F.metric s) hη hc Q (U t)) hU
    ((metricEntropyGradientLp_time_continuousOn F isCompact_Icc hJ hη hc Q (U t)
      t ⟨ht.1.le, ht.2.le⟩).continuousAt (Icc_mem_nhds ht.1 ht.2))
    (metricEntropyPotential_field_hasDerivAt F hJ ht hη hc hQ (U t)) (C := C)
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  apply fieldIntegral_remainder_le _ (metricEntropyPotential_integrable (F.metric s) hη hc hQ)
    (U t) (U s) (metricEntropyGradientLp (F.metric s) hη hc Q (U t))
  filter_upwards [metricEntropyGradientLp_coe (F.metric s) hη hc Q (U t)] with x hx
  rw [hx, metricEntropyGradient_pair]
  exact hR s hs x (U t x) (U s x)

theorem metric_form_entropy_chain_rate {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (Q : ℝ)
    (u z w : PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hz : ∀ j : Fin n, (dirichletInclusion K (z j) : Lp ℝ 2 (volume : Measure V)) =ᵐ[volume]
      fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1) (x, dirichletFieldValue K u x))
    (heq : inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) w) =
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (rawLowerFormOperator D hK η hη u) -
        principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u) :
    fieldIntegral (metricEntropyTimePotential D η Q) (dirichletFieldValue K u) +
      inner ℝ (metricEntropyGradientLp g η.smooth' hη Q (dirichletFieldValue K u))
        (dirichletFieldValue K w) = rawEntropyFormRate hK D η hη Q u z := by
  have hg := metricEntropyGradientLp_eq_form_test g η.smooth' hη Q u z hz
  have hp := congrArg (fun f : L2V => inner ℝ f (dirichletFieldValue K w)) hg
  have he := (hp.trans (dirichletFieldValue_inner K z w)).trans heq
  exact (congrArg (fun r : ℝ =>
    fieldIntegral (metricEntropyTimePotential D η Q) (dirichletFieldValue K u) + r) he).trans
      (add_comm _ _)

theorem raw_form_entropy_hasDerivAt_nonpos {J : Set ℝ} (F : RicciFlow n V J)
    {a b t : ℝ} (hJ : Icc a b ⊆ J) (ht : t ∈ Ioo a b)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) {Q : ℝ} (hQ : 0 ≤ Q)
    (hR : ∀ x, 0 ≤ (F.connection t).scalarCurvature x)
    (W : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K))
    (hW : DifferentiableAt ℝ W t)
    (heq : ∀ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
        (finiteHilbertMap (dirichletInclusion K) (deriv W t)) =
          inner ℝ (finiteHilbertMap (dirichletInclusion K) z)
            (rawLowerFormOperator (F.connection t) hK.isClosed η hη (W t)) -
              principalVectorEnergy K (rawCutoffPrincipalCoefficient (F.metric t) η hη) z (W t)) :
    ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt
      (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q)
        (dirichletFieldValue K (W s))) d t := by
  obtain ⟨z, hz, hnonpos⟩ := exists_metric_entropy_dissipating_test hK
    (F.connection t) η hη hηK hQ hR (W t)
  refine ⟨rawEntropyFormRate hK.isClosed (F.connection t) η hη Q (W t) z, hnonpos, ?_⟩
  have hfield := (dirichletFieldValue K).hasFDerivAt.comp_hasDerivAt t hW.hasDerivAt
  have hchain := metricEntropy_field_time_chain F hJ ht η.smooth' hη hQ
    (fun s => dirichletFieldValue K (W s)) hfield
  exact (metric_form_entropy_chain_rate hK.isClosed (F.connection t) η hη Q
    (W t) z (deriv W t) hz (heq z)) ▸ hchain

end PoincareConjecture.M35.Uniqueness.Heat
