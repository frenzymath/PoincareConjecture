import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.LimitEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderAssembly










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace NormalizedKappaSpacetimeEmbedding


noncomputable def terminalPullbackCoefficients
    {kappa : ℝ} {source target : BasedKappaSolution kappa}
    {U : Set target.carrier.carrier}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (Iic 0 ×ˢ U))
    (q : target.carrier.carrier) (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := by
  let c := extChartAt (𝓡 3) q
  let f := fun y ↦ (e.toFun (0, y)).2
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (f (c.symm z))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (f (c.symm z))) := by
    unfold TangentSpace
    infer_instance
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (f (c.symm z)) :=
    (mfderiv (𝓡 3) (𝓡 3) f (c.symm z)).comp
    (mfderiv (𝓡 3) (𝓡 3) c.symm z)
  exact ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 3) (f (c.symm z)))
    (F := TangentSpace (𝓡 3) (f (c.symm z))) (G := ℝ)
    (E' := EuclideanSpace ℝ (Fin 3)) (F' := EuclideanSpace ℝ (Fin 3))
    ((source.flow.flow.metric 0).inner (f (c.symm z))) A A

end NormalizedKappaSpacetimeEmbedding

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem terminalPullbackCoefficients_tendstoUniformlyOn
    (hconv : M23TerminalMetricConvergence G e)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hchart : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn (fun k ↦ (e k).terminalPullbackCoefficients q)
      ((G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm)
      atTop K := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hK.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono hchart))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨N, _, hN⟩ := hconv q j 0 ({0} ×ˢ K) (isCompact_singleton.prod hK)
    (by
      rintro ⟨t, z⟩ ⟨ht, hz⟩
      refine ⟨?_, hchart hz, hj (mem_image_of_mem _ hz)⟩
      exact (mem_singleton_iff.mp ht).le)
    (epsilon / 10) (by positivity)
  filter_upwards [eventually_ge_atTop N] with k hk z hz
  rw [dist_eq_norm, norm_sub_rev]
  have hentry (a b : Fin 3) :
      |((e k).terminalPullbackCoefficients q z -
          (G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm z)
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ epsilon / 10 := by
    have h := hN k hk a b (0, z) ⟨mem_singleton 0, hz⟩
    dsimp only [M23TerminalMetricJet] at h
    rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm] at h
    exact h.le
  have hnorm := HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries
    ((e k).terminalPullbackCoefficients q z -
      (G.limit.flow.flow.metric 0).pullbackCoefficients (extChartAt (𝓡 3) q).symm z)
    (by positivity : 0 ≤ epsilon / 10) hentry
  exact hnorm.trans_lt (by norm_num; linarith)



theorem eventually_local_inner_le_twice
    (hconv : M23TerminalMetricConvergence G e) (p : G.limit.carrier.carrier) :
    ∃ V ∈ 𝓝 p, ∀ᶠ k in atTop, ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
      normalizedKappaPullbackInnerValue (e k) 0 x v v ≤
        2 * (G.limit.flow.flow.metric 0).inner x v v := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) p
  let g := G.limit.flow.flow.metric 0
  have hpc : p ∈ c.source := mem_extChartAt_source p
  obtain ⟨K, hKnhds, hKt, hK⟩ := local_compact_nhds
    ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (c.map_source hpc))
  have hcont : ContinuousOn (g.pullbackCoefficients c.symm) K := by
    intro z hz
    exact (g.contDiffAt_pullbackCoefficients
      ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) p).mem_nhds (hKt hz)))).continuousAt.continuousWithinAt
  have hpos : ∀ z ∈ K, ∀ w : E, w ≠ 0 → 0 < g.pullbackCoefficients c.symm z w w := by
    intro z hz w hw
    apply g.pos
    have hcomp := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := 𝓡 3) (hKt hz)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hcomp
    intro hzero
    have h := congrArg (fun L ↦ L w) hcomp
    change mfderiv (𝓡 3) (𝓡 3) c (c.symm z)
      (mfderiv (𝓡 3) (𝓡 3) c.symm z w) = w at h
    erw [hzero, map_zero] at h
    exact hw h.symm
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hcont hpos
  have hcoeff := Metric.tendstoUniformlyOn_iff.mp
    (hconv.terminalPullbackCoefficients_tendstoUniformlyOn p hK hKt) a ha
  let V := c.source ∩ c ⁻¹' K
  have hV : V ∈ 𝓝 p := inter_mem
    ((isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds hpc)
    ((continuousAt_extChartAt (I := 𝓡 3) p).preimage_mem_nhds hKnhds)
  refine ⟨V, hV, ?_⟩
  filter_upwards [hcoeff] with k hk x hx v
  let w := mfderiv (𝓡 3) (𝓡 3) c x v
  have hnorm : ‖(e k).terminalPullbackCoefficients p (c x) -
      g.pullbackCoefficients c.symm (c x)‖ ≤ a := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hk (c x) hx.2).le
  have herr : |(e k).terminalPullbackCoefficients p (c x) w w -
      g.pullbackCoefficients c.symm (c x) w w| ≤ a * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖(e k).terminalPullbackCoefficients p (c x) -
          g.pullbackCoefficients c.symm (c x)‖ * ‖w‖ * ‖w‖ := by
        simpa only [sub_apply, Real.norm_eq_abs] using
          ((e k).terminalPullbackCoefficients p (c x) -
            g.pullbackCoefficients c.symm (c x)).le_opNorm₂ w w
      _ ≤ a * ‖w‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg w) (norm_nonneg w))
  have hbound : (e k).terminalPullbackCoefficients p (c x) w w ≤
      2 * g.pullbackCoefficients c.symm (c x) w w := by
    have hh := (abs_le.mp herr).2
    linarith [hlower (c x) hx.2 w]
  have hderiv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 3) hx.1
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hderiv
  have hv : mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w = v :=
    congrArg (fun L ↦ L v) hderiv
  have hcx : c.symm (c x) = x := c.left_inv hx.1
  change normalizedKappaPullbackInnerValue (e k) 0 (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) ≤
    2 * g.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) at hbound
  erw [hv, hcx] at hbound
  exact hbound



theorem eventually_inner_le_twice_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      normalizedKappaPullbackInnerValue (e k) 0 x v v ≤
        2 * (G.limit.flow.flow.metric 0).inner x v v := by
  classical
  choose V hV hbound using hconv.eventually_local_inner_le_twice
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover V (fun x _ ↦ hV x)
  have hall := s.eventually_all.mpr (fun x _ ↦ hbound x)
  filter_upwards [hall] with k hk x hx v
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
  exact hk p hp x hxp v

end M23TerminalMetricConvergence

end PoincareConjecture
