import PoincareConjecture.Proofs.M47.LimitFiniteEndpointOldMetric
import PoincareConjecture.Proofs.M47.LimitFiniteEndpointComplete
import PoincareConjecture.Proofs.M47.TerminalCurvatureOriginalCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance endpointReadoutDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointReadoutDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance endpointReadoutBilinAdd :
    NormedAddCommGroup Bilin := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance endpointReadoutBilinSpace :
    NormedSpace ℝ Bilin := ContinuousLinearMap.toNormedSpace

theorem limitFinite_endpoint_original_charts
    {ι : Type v} {X : Type u} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X]
    (U : ι → TopologicalSpace.Opens X) (W : ι → Set E) (hW : ∀ i, IsOpen (W i))
    (Phi : ∀ i, PartialDiffeomorph (𝓡 3) (𝓡 3) E (U i) ∞)
    (hsub : ∀ i, W i ⊆ (Phi i).source)
    (hcover : ∀ x : X, ∃ i, x ∈ (fun z : E => (Phi i z).val) '' W i) :
    ∃ c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞,
      (∀ i, ((c i).symm : E → X) = fun z => (Phi i z).val) ∧
      (∀ i, (c i).source = (fun z : E => (Phi i z).val) '' W i ∧
        (c i).target = W i) ∧ (∀ x : X, ∃ i, x ∈ (c i).source) := by
  have hembed (i : ι) :
      Topology.IsOpenEmbedding (fun z : W i => (Phi i z).val) := by
    have hincl := Topology.IsOpenEmbedding.inclusion (hsub i)
      ((hW i).preimage continuous_subtype_val)
    exact (U i).isOpen.isOpenEmbedding_subtypeVal.comp
      ((Phi i).toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp hincl)
  have hlocal (i : ι) : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞
      (fun z : E => (Phi i z).val) (W i) := by
    intro z
    exact ((Phi i).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsub i z.property)).comp
      (𝓡 3) X (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i) (Phi i z))
  obtain ⟨c, hc⟩ := terminalCurvature_exists_original_partial_charts W hW
    (fun i z => (Phi i z).val) hembed hlocal
  refine ⟨c, fun i => (hc i).1, fun i => (hc i).2, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨i, (hc i).2.1.symm ▸ hi⟩

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance endpointReadoutTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance endpointReadoutCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance endpointReadoutManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

theorem limitFinite_endpoint_inner_chart_metric
    (hfinite : H ≠ ⊤) (dStage : ℕ → ℝ) (hdStage : ∀ m, 0 < dStage m)
    (AStage : ∀ m, RicciFlow 3 (U m)
      (Ioo (-H.toReal - dStage m / 8) (-H.toReal + dStage m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((AStage m).metric (-H.toReal)).inner x v w = gE.inner x.val v w)
    (hold : ∀ m t, t ∈ Ioo (-H.toReal - dStage m / 8) (-H.toReal + dStage m / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((AStage m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val v w)
    (j : ℕ) {d R rho : ℝ} (hd : 0 < d) (hrhoR : rho < R)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E (U j) ∞)
    (hsource : Phi.source = Metric.ball 0 R)
    (A : ℕ → RicciFlow 3 (U j) (Icc (-(H.toReal + d / 2)) 0))
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma)
    (hread : ∀ t, t ∈ Ioo (-H.toReal - d / 8) (-H.toReal + d / 4) →
      t ∈ blowupBackwardInterval H → ∀ᶠ k in atTop,
        ∃ htk : t ∈ Icc (-G.exhaustion.time (sigma k)) 0,
          ∀ (x : U j) (v w : E), ((A (sigma k)).metric t).inner x v w =
            (G.embedding (sigma k)).pullbackInner t htk x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier) x w))
    (B : ℝ × E → Bilin)
    (hB : ContDiffOn ℝ ∞ B (Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho))
    (hjets : ∀ r K, IsCompact K →
      K ⊆ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ r (fun p : ℝ × E =>
          ((A (sigma k)).metric (p.1 + (-H.toReal + d / 4))).pullbackCoefficients Phi p.2))
        (iteratedFDeriv ℝ r B) atTop K) :
    EqOn (fun z => B (-d / 4, z))
      (gE.pullbackCoefficients (fun z : E => (Phi z).val)) (Metric.ball 0 rho) := by
  classical
  have hH : 0 < H := by simpa using G.limit.zero_mem.2
  have hT := limitFinite_horizon_pos hH hfinite
  let c := -H.toReal + d / 4
  have hpoint (p : ℝ × E)
      (hp : p ∈ Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho) :
      Tendsto (fun k => ((A (sigma k)).metric (p.1 + c)).pullbackCoefficients Phi p.2)
        atTop (𝓝 (B p)) := by
    have h := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × E)).comp_tendstoUniformlyOn
        (hjets 0 {p} isCompact_singleton (singleton_subset_iff.mpr hp))
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      h.tendsto_at (mem_singleton p)
  intro z hz
  have hzPhi : z ∈ Phi.source := by
    rw [hsource]
    exact Metric.ball_subset_ball hrhoR.le hz
  have hx : (Phi z).val ∈ ⋃ m, G.exhaustion.space m := by
    rw [G.exhaustion.space_covers]
    exact mem_univ _
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  let y : U m := ⟨(Phi z).val, hm⟩
  have hcomp := mfderiv_comp z
    ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U j)).mdifferentiable
      (by simp) (Phi z)) (Phi.mdifferentiableAt (by simp) hzPhi)
  have ht0 : -H.toReal ∈ Ioo (-H.toReal - dStage m / 8) (-H.toReal + dStage m / 4) :=
    ⟨by linarith [hdStage m], by linarith [hdStage m]⟩
  have htRow : -H.toReal ∈ Ioo (-H.toReal - d / 8) (-H.toReal + d / 4) :=
    ⟨by linarith, by linarith⟩
  have hp0 : (-H.toReal - c, z) ∈
      Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho := by
    refine ⟨⟨?_, ?_⟩, hz⟩ <;> dsimp [c] <;> linarith
  ext v w
  let a : E := mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier)
    (Phi z) (mfderiv (𝓡 3) (𝓡 3) Phi z v)
  let b : E := mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U j → G.limit.sliceCarrier.carrier)
    (Phi z) (mfderiv (𝓡 3) (𝓡 3) Phi z w)
  have hlimA : Tendsto (fun t => ((AStage m).metric t).inner y a b)
      (𝓝[>] (-H.toReal)) (𝓝 (((AStage m).metric (-H.toReal)).inner y a b)) :=
    (((AStage m).equation (-H.toReal) ht0 y a b).hasDerivAt
      (isOpen_Ioo.mem_nhds ht0)).continuousAt.mono_left nhdsWithin_le_nhds
  have htimeCont : ContinuousAt (fun t : ℝ => (t - c, z)) (-H.toReal) := by fun_prop
  have hcontB : ContinuousAt (fun t : ℝ => B (t - c, z)) (-H.toReal) :=
    (hB.continuousOn.continuousAt
      ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hp0)).comp
        (f := fun t : ℝ => (t - c, z)) htimeCont
  have hlimB : Tendsto (fun t : ℝ => B (t - c, z) v w) (𝓝[>] (-H.toReal))
      (𝓝 (B (-H.toReal - c, z) v w)) :=
    (((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto _).comp
        hcontB.tendsto)).mono_left nhdsWithin_le_nhds
  have heq : (fun t : ℝ => B (t - c, z) v w) =ᶠ[𝓝[>] (-H.toReal)]
      (fun t => ((AStage m).metric t).inner y a b) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht0),
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds htRow),
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (neg_lt_zero.mpr hT)),
      self_mem_nhdsWithin] with t htStage htRow htneg htright
    have htOld : t ∈ blowupBackwardInterval H := by
      rw [limitFinite_domain_eq hfinite]
      exact ⟨htright, htneg.le⟩
    have hp : (t - c, z) ∈
        Ioo (-((3 * d / 4) / 2)) 0 ×ˢ Metric.ball 0 rho := by
      refine ⟨⟨?_, ?_⟩, hz⟩ <;> dsimp [c] <;> linarith [htRow.1, htRow.2]
    have hcv (v w : E) : Tendsto
        (fun k => ((A (sigma k)).metric t).pullbackCoefficients Phi z v w)
        atTop (𝓝 (B (t - c, z) v w)) := by
      have h := ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
        (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto _).comp (hpoint _ hp))
      simpa only [sub_add_cancel, Function.comp_def, ContinuousLinearMap.apply_apply] using h
    have hOld := limitFinite_endpoint_old_metric G j sigma hsigma htOld
      (fun k => (A (sigma k)).metric t) (hread t htRow htOld) Phi z (B (t - c, z)) hcv
    rw [hOld, hold m t htStage htOld y a b]
    change (G.limit.flow.metric t).inner (Phi z).val _ _ = _
    rfl
  have h := tendsto_nhds_unique hlimB (hlimA.congr' heq.symm)
  rw [hendpoint m y a b] at h
  have hclock : -H.toReal - c = -d / 4 := by dsimp [c]; ring
  rw [hclock] at h
  have hv : mfderiv (𝓡 3) (𝓡 3) (fun z : E => (Phi z).val) z v = a :=
    congrArg (fun L => L v) hcomp
  have hw : mfderiv (𝓡 3) (𝓡 3) (fun z : E => (Phi z).val) z w = b :=
    congrArg (fun L => L w) hcomp
  change B (-d / 4, z) v w = gE.inner (Phi z).val _ _
  exact h.trans (congrArg₂ (fun (a b : E) => gE.inner (Phi z).val a b) hv.symm hw.symm)

end PoincareConjecture.M47
