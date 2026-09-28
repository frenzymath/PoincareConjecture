import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.MetricTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Horns
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

namespace StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem isPreconnected_carrier (horn : StrongHorn E epsilon) :
    IsPreconnected horn.carrier := by
  have heq : horn.carrier = horn.parameterization '' (univ ×ˢ Ico (0 : ℝ) 1) := by
    ext x
    constructor
    · intro hx
      let z := horn.coordinate.symm ⟨x, hx⟩
      exact ⟨(z.1, z.2), ⟨mem_univ _, z.2.property⟩,
        horn.parameterization_coordinate_symm ⟨x, hx⟩⟩
    · rintro ⟨⟨s, t⟩, ⟨_, ht⟩, rfl⟩
      have hx := (horn.coordinate (s, ⟨t, ht⟩)).property
      rwa [horn.coordinate_eq] at hx
  rw [heq]
  apply (isPreconnected_univ.prod isPreconnected_Ico).image
  apply horn.parameterization_smooth.continuousOn.mono
  intro z hz
  exact ⟨hz.1, (neg_lt_zero.mpr horn.collar_pos).trans_le hz.2.1, hz.2.2⟩

theorem carrier_not_subset_compact (horn : StrongHorn E epsilon)
    (K : Set (E.extended.slice T).carrier) (hK : IsCompact K) :
    ¬ horn.carrier ⊆ K := by
  intro hsub
  exact horn.tail_not_subset_compact 0 (by norm_num) K hK
    ((horn.coordinateTail_subset_carrier le_rfl).trans hsub)

end StrongHorn

namespace GeneralizedBlowupConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

theorem not_isCompact_univ_of_source_regions (G : GeneralizedBlowupConvergence S J)
    (U : ∀ k, Set ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier)
    (hU : ∀ k, IsPreconnected (U k))
    (hescape : ∀ k K, IsCompact K → ¬ U k ⊆ K)
    (hballs : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop, S.baseBall (G.subsequence k) A ⊆ U k) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  intro hcompact
  let g := G.limit.flow.metric 0
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : G.limit.carrier.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : G.limit.carrier.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace G.limit.carrier.carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) _
  let : MetricSpace G.limit.carrier.carrier := EMetricSpace.toMetricSpace
    (fun x y => g.edist_ne_top x y)
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.subset_ball_lt 0 G.limit.base
  have hball : ∀ x : G.limit.carrier.carrier,
      g.edist G.limit.base x < ENNReal.ofReal R := by
    intro x
    have hx := hbound (mem_univ x)
    change (g.edist x G.limit.base).toReal < R at hx
    rw [show g.edist x G.limit.base = g.edist G.limit.base x from
      Manifold.riemannianEDist_comm] at hx
    exact (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top _ _)).mpr hx
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hev := (G.eventually_zero_tangentNorm_bounds hcompact (C := 2) (by norm_num)).and
    ((hballs (2 * R) (by positivity)).and (eventually_ge_atTop j))
  obtain ⟨k, hk, hUk, hjk⟩ := hev.exists
  let e := G.zeroSliceEmbedding k
  let h := G.zeroSourceMetric k
  have hfull : e.source = univ := by
    apply eq_univ_of_univ_subset
    simpa only [e, G.zeroSliceEmbedding_source] using
      hj.trans (G.exhaustion.space_increasing hjk)
  have he : ContMDiff (𝓡 3) (𝓡 3) 1 e := by
    apply contMDiffOn_univ.mp
    have he' : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := by
      simpa only [e, G.zeroSliceEmbedding_source] using G.zeroSliceEmbedding_smooth k
    rw [hfull] at he'
    exact he'.of_le (by simp)
  have himage : e '' univ ⊆ U k := by
    rintro y ⟨x, _, rfl⟩
    apply hUk
    rw [← G.zeroSourceMetric_ball]
    have hd := g.edist_le_mul_of_tangentNorm_mfderiv_le h he (by norm_num : (0 : ℝ) < 2)
      (fun z v => (hk z (mem_univ z) v).1) G.limit.base x
    rw [G.zeroSliceEmbedding_base] at hd
    change h.edist (S.base (G.subsequence k)).2 (e x) < ENNReal.ofReal (2 * R)
    apply hd.trans_lt
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top (hball x)
  have hK : IsCompact (e '' univ) := hcompact.image he.continuous
  have hKo : IsOpen (e '' univ) :=
    e.isOpen_image_of_subset_source isOpen_univ (by rw [hfull])
  have hmeet : (U k ∩ e '' univ).Nonempty :=
    ⟨e G.limit.base, himage (mem_image_of_mem e (mem_univ _)),
      mem_image_of_mem e (mem_univ _)⟩
  exact hescape k (e '' univ) hK ((hU k).subset_isClopen ⟨hK.isClosed, hKo⟩ hmeet)

end GeneralizedBlowupConvergence

namespace DeepHorn

attribute [local instance] FlowCarrier.topologicalSpace

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}

theorem terminalBlowupSequence_limit_not_isCompact
    (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
    (Q : ∀ k, SingularLimitConclusion (H k))
    (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
    (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
    (hdiv : Tendsto (fun k =>
      ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)
    (hM04 : RicciFlowCurvatureCalculus.{u}) {K B epsilon : ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension epsilon)
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K)
    {J : Set ℝ} (G : GeneralizedBlowupConvergence
      (terminalBlowupSequence H Q x hpos hdiv) J) :
    ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
  apply G.not_isCompact_univ_of_source_regions
    (fun k => (horn (G.subsequence k)).carrier)
    (fun k => (horn (G.subsequence k)).isPreconnected_carrier)
    (fun k => (horn (G.subsequence k)).carrier_not_subset_compact)
  intro A hA
  exact G.subsequence_strictMono.tendsto_atTop.eventually
    (terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv
      hM04 hK hB hcutoff hconstant horn hx hboundary A hA)

end DeepHorn

end PoincareConjecture
