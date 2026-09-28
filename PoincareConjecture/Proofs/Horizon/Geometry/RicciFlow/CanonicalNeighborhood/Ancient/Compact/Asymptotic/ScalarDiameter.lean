import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.Noncompact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.RescalingGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem AncientRescaling.metricDiameter_scale {tau : ℝ}
    (R : AncientRescaling K tau) (hcompact : IsCompact (univ : Set M))
    {t : ℝ} (ht : t < 0) :
    metricDiameter (R.flow.metric t) univ =
      Real.sqrt (1 / tau) * metricDiameter (K.flow.metric (tau * t)) univ := by
  unfold metricDiameter
  simp_rw [R.edist_scale t ht, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact ((OrderIso.mulLeft₀ (Real.sqrt (1 / tau))
    (Real.sqrt_pos.mpr (one_div_pos.mpr R.tau_pos))).map_ciSup
      (compact_metricDiameter_bddAbove (K.flow.metric (tau * t)) hcompact)).symm

theorem AncientRescaling.scalarDiameter_eq {tau : ℝ}
    (R : AncientRescaling K tau) (hcompact : IsCompact (univ : Set M))
    {t : ℝ} (ht : t < 0) (p : M) :
    metricDiameter (R.flow.metric t) univ *
        Real.sqrt ((R.flow.connection t).scalarCurvature p) =
      metricDiameter (K.flow.metric (tau * t)) univ *
        Real.sqrt ((K.flow.connection (tau * t)).scalarCurvature p) := by
  rw [R.metricDiameter_scale hcompact ht, R.scalar_scale t ht,
    Real.sqrt_mul R.tau_pos.le, one_div, Real.sqrt_inv]
  have hne : Real.sqrt tau ≠ 0 := (Real.sqrt_pos.mpr R.tau_pos).ne'
  field_simp

namespace AncientCompactTimeConvergence

variable {S : AncientRescalingSequence K} (G : AncientCompactTimeConvergence S)

theorem tendsto_scalarDiameter_of_noncompact_limit
    (hcompact : IsCompact (univ : Set M))
    (hnoncompact : ¬ IsCompact (univ : Set G.limit.carrier.carrier))
    {t : ℝ} (ht : t < 0) (p : G.limit.carrier.carrier)
    (hp : 0 < (G.limit.flow.connection t).scalarCurvature p) :
    Tendsto (fun k ↦
      metricDiameter (K.flow.metric (S.scale (G.subsequence k) * t)) univ *
        Real.sqrt ((K.flow.connection (S.scale (G.subsequence k) * t)).scalarCurvature
          ((G.embedding k).toFun (t, p)).2)) atTop atTop := by
  have h := Tendsto.atTop_mul_pos (Real.sqrt_pos.mpr hp)
    (G.tendsto_metricDiameter_of_noncompact_limit hcompact hnoncompact ht)
    (G.tendsto_scalarCurvature t ht p).sqrt
  simpa only [(S.rescaling _).scalarDiameter_eq hcompact ht] using h

end AncientCompactTimeConvergence

theorem compact_nonround_eventually_large_past_scalarDiameter
    (P : M26CanonicalNeighborhoodPredecessors.{u})
    (hcompact : IsCompact (univ : Set M))
    (hnonround : ¬ IsRoundAncientKappaSolution K)
    (S : AncientRescalingSequence K) (L : AncientAsymptoticSolitonLimitData S)
    (C : ℝ) :
    ∀ᶠ k in atTop, ∃ p : M,
      C < metricDiameter (K.flow.metric (-S.scale (L.convergence.subsequence k))) univ *
        Real.sqrt ((K.flow.connection (-S.scale (L.convergence.subsequence k))).scalarCurvature p) := by
  obtain ⟨p, hp⟩ := L.nonflat_at (-1) (by norm_num)
  have hR : 0 < (L.convergence.limit.flow.connection (-1)).scalarCurvature p :=
    (lt_of_le_of_ne (Real.sqrt_nonneg _) hp.symm).trans_le
      ((L.convergence.limit.flow.connection (-1)).curvatureTensorNorm_le_scalarCurvature_sharp
        (L.convergence.limit.flow.connection (-1)).intrinsicCurvatureTensorCalculus p
        (L.convergence.limit.nonnegative_curvature_operator (-1) (by norm_num) p))
  have hd := L.convergence.tendsto_scalarDiameter_of_noncompact_limit hcompact
    (compact_nonround_asymptotic_limit_noncompact P K hnonround S L)
    (by norm_num : (-1 : ℝ) < 0) p hR
  filter_upwards [hd.eventually (eventually_gt_atTop C)] with k hk
  refine ⟨((L.convergence.embedding k).toFun (-1, p)).2, ?_⟩
  exact lt_of_lt_of_eq hk (congrArg (fun t ↦
    metricDiameter (K.flow.metric t) univ *
      Real.sqrt ((K.flow.connection t).scalarCurvature
        ((L.convergence.embedding k).toFun (-1, p)).2)) (mul_neg_one _))

end PoincareConjecture
