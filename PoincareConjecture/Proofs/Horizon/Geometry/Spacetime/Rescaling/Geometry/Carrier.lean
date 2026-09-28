import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Geometry.Slices
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Interval.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Atlas.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.GeometryTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u v

open PoincareConjecture.Homothety

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

noncomputable def rescaledCylinderMap (T : SpacetimeIntervalSystem)
    (b : A.box_index) :
    (T.interval (parabolicInterval Q hQ a (A.box b).interval)).Point ×
        (A.box b).spatial →
      (T.interval (A.box b).interval).Point × (A.box b).spatial :=
  fun p ↦ (
    ((parabolicIntervalTransport T Q hQ a).diffeomorph (A.box b).interval).symm p.1,
    p.2)

theorem rescaledCylinderMap_val (T : SpacetimeIntervalSystem)
    (b : A.box_index) (p :
      (T.interval (parabolicInterval Q hQ a (A.box b).interval)).Point ×
        (A.box b).spatial) :
    ((rescaledCylinderMap T b p).1 : ℝ) = parabolicTimeInv Q a (p.1 : ℝ) := by
  change (((parabolicIntervalTransport T Q hQ a).diffeomorph (A.box b).interval).symm p.1 : ℝ) = _
  rw [ParabolicIntervalTransport.inverse_eq]
  rfl

theorem rescaledCylinderMap_fiber (T : SpacetimeIntervalSystem)
    (b : A.box_index) (p :
      (T.interval (parabolicInterval Q hQ a (A.box b).interval)).Point ×
        (A.box b).spatial) :
    (rescaledCylinderMap T b p).2 = p.2 := by rfl

theorem scaled_reparameterized_smooth
    {M : Type v} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (I : SpacetimeInterval) (g : ℝ → RiemannianMetric n M)
    (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    RiemannianMetric.IsSmoothFamilyOn
      (fun s ↦ scaleSmoothMetric (g (parabolicTimeInv Q a s)) Q hQ)
      (parabolicInterval Q hQ a I).domain := by
  unfold RiemannianMetric.IsSmoothFamilyOn at hg ⊢
  let r : ℝ × M → ℝ × M := fun p ↦ (parabolicTimeInv Q a p.1, p.2)
  let sold : ℝ × M → Bundle.TotalSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
    fun p ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p.2 ((g p.1).inner p.2)
  let snew : ℝ × M → Bundle.TotalSpace
      (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
    fun p ↦ Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p.2 ((scaleSmoothMetric (g (parabolicTimeInv Q a p.1)) Q hQ).inner p.2)
  have hr : ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) ((𝓘(ℝ)).prod (𝓡 n)) ∞ r := by
    have ht : ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) 𝓘(ℝ) ∞
        (fun p : ℝ × M ↦ parabolicTimeInv Q a p.1) := by
      change ContMDiff ((𝓘(ℝ)).prod (𝓡 n)) 𝓘(ℝ) ∞
        (fun p : ℝ × M ↦ a + p.1 / Q)
      have hclock : ContDiff ℝ ∞ (fun t : ℝ ↦ a + t / Q) :=
        contDiff_const.add (contDiff_id.div_const Q)
      exact hclock.contMDiff.comp contMDiff_fst
    exact ht.prodMk contMDiff_snd
  have hmap : (parabolicInterval Q hQ a I).domain ×ˢ Set.univ ⊆
      r ⁻¹' (I.domain ×ˢ Set.univ) := by
    intro p hp
    exact ⟨(mem_parabolicInterval_iff Q hQ a I p.1).1 hp.1, trivial⟩
  have hcomp : ContMDiffOn ((𝓘(ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (sold ∘ r) ((parabolicInterval Q hQ a I).domain ×ˢ Set.univ) := by
    exact hg.comp hr.contMDiffOn hmap
  intro p hp
  have hold := Bundle.contMDiffWithinAt_totalSpace.mp (hcomp p hp)
  let e := trivializationAt
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2
  have hbase : (fun q : ℝ × M ↦ q.2) ⁻¹' e.baseSet ∈
      𝓝[(parabolicInterval Q hQ a I).domain ×ˢ Set.univ] p := by
    apply mem_nhdsWithin_of_mem_nhds
    exact (continuousAt_snd.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt _ _ _)))
  let : ∀ x : M, IsTopologicalAddGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : ∀ x : M, IsTopologicalAddGroup
      (TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : ∀ x : M, ContinuousAdd (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    exact (inferInstance :
      IsTopologicalAddGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ)).toContinuousAdd
  let : ∀ x : M, ContinuousSMul ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := by
    intro x
    infer_instance
  let : e.IsLinear ℝ := by
    dsimp [e]
    rw [hom_trivializationAt]
    refine ⟨?_⟩
    intro b hb
    exact (Bundle.Pretrivialization.continuousLinearMap.isLinear
      (RingHom.id ℝ)
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.2)
      (trivializationAt (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2)).linear b hb
  have hcoord := (contMDiffWithinAt_const (I := (𝓘(ℝ)).prod (𝓡 n))
      (I' := 𝓘(ℝ)) (n := ∞) (x := p) (c := Q)).smul hold.2
  change ContMDiffWithinAt ((𝓘(ℝ)).prod (𝓡 n))
    ((𝓡 n).prod 𝓘(ℝ,
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
    snew ((parabolicInterval Q hQ a I).domain ×ˢ Set.univ) p
  refine Bundle.contMDiffWithinAt_totalSpace.mpr ⟨?_, ?_⟩
  · exact contMDiffWithinAt_snd
  · refine hcoord.congr_of_eventuallyEq ?_ ?_
    · apply Filter.eventually_of_mem
      · exact hbase
      · intro q hq
        change q.2 ∈ e.baseSet at hq
        change (e (snew q)).2 = Q • (e (sold (r q))).2
        apply (e.linear ℝ hq).2
    · change (e (snew p)).2 = Q • (e (sold (r p))).2
      apply (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' p.2)).2

noncomputable def transportedCylinder
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (E : CompatibleSpacetimeCylinder R.spacetime
      (R.timeIntervals.interval K) C) :
    CompatibleSpacetimeCylinder
      (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a K)) C := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let F := P.diffeomorph K
  let d := F.symm.prodCongr (Diffeomorph.refl (𝓡 n) C ∞)
  have hd_smooth : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ d :=
    d.contMDiff
  refine {
    interval_subset := ?_
    toSpacetime := fun p ↦ E.toSpacetime (d p)
    embedding := E.embedding.comp d.toHomeomorph.isEmbedding
    time_eq := ?_
    worldline_smooth := ?_
    worldline_derivative := ?_
    smooth := E.smooth.comp hd_smooth
    differential_injective := ?_ }
  · exact parabolicInterval_subset Q hQ a K A.interval E.interval_subset
  · intro p
    change parabolicTime Q a (R.spacetime.timeFunction (E.toSpacetime (d p))) = p.1.val
    rw [E.time_eq]
    change parabolicTime Q a
      (((P.diffeomorph K).symm p.1 : _).val) = p.1.val
    rw [P.inverse_eq]
    exact parabolicTime_parabolicTimeInv Q hQ a p.1.val
  · intro x
    exact (E.worldline_smooth x).comp F.symm.contMDiff
  · intro t x
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      ((fun s : (R.timeIntervals.interval K).Point ↦ E.toSpacetime (s, x)) ∘ F.symm) t
      ((R.timeIntervals.interval (parabolicInterval Q hQ a K)).positiveTangent t) = _
    rw [mfderiv_comp t ((E.worldline_smooth x).mdifferentiable (by simp) _)
      (F.symm.mdifferentiable (by simp) _)]
    change mfderiv (𝓡∂ 1) (spacetimeModel n)
      (fun s : (R.timeIntervals.interval K).Point ↦ E.toSpacetime (s, x)) (F.symm t)
      (mfderiv (𝓡∂ 1) (𝓡∂ 1) F.symm t
        ((R.timeIntervals.interval (parabolicInterval Q hQ a K)).positiveTangent t)) = _
    rw [P.inverse_derivative, map_smul, E.worldline_derivative]
    rfl
  · intro p u v huv
    have hcomp := mfderiv_comp p
      (E.smooth.mdifferentiable (by simp) _) (hd_smooth.mdifferentiable (by simp) _)
    have hdv : mfderiv (spacetimeModel n) (spacetimeModel n) d p u =
        mfderiv (spacetimeModel n) (spacetimeModel n) d p v := by
      apply E.differential_injective (d p)
      have huv' := huv
      change (mfderiv (spacetimeModel n) (spacetimeModel n)
        (E.toSpacetime ∘ d) p) u =
        (mfderiv (spacetimeModel n) (spacetimeModel n)
          (E.toSpacetime ∘ d) p) v at huv'
      rw [hcomp] at huv'
      exact huv'
    exact (d.mfderivToContinuousLinearEquiv (by simp) p).injective hdv

noncomputable def rescaledCylinder (b : A.box_index) :
    CompatibleSpacetimeCylinder
      (parabolicSpacetime R.spacetime Q hQ a)
      (R.timeIntervals.interval (parabolicInterval Q hQ a (A.box b).interval))
      (A.box b).spatial :=
  transportedCylinder (R := R) (Q := Q) (hQ := hQ) (a := a)
    (A.box b).interval (R.boxCylinder b)

noncomputable def transportedCylinderMetric
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
    (K : SpacetimeInterval)
    (E : CompatibleSpacetimeCylinder R.spacetime
      (R.timeIntervals.interval K) C)
    (G : SpacetimeCylinderMetric E) :
    SpacetimeCylinderMetric (transportedCylinder (R := R) (Q := Q) (hQ := hQ)
      (a := a) K E) := by
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  let g : ℝ → RiemannianMetric n C :=
    fun s ↦ scaleSmoothMetric (G.metric (parabolicTimeInv Q a s)) Q hQ
  refine {
    metric := g
    smooth := ?_
    spatialTangentEquiv := ?_
    spatialTangentEquiv_eq := ?_
    metric_eq := ?_ }
  · exact scaled_reparameterized_smooth K G.metric G.smooth Q hQ a
  · intro t x
    exact (G.spatialTangentEquiv ((P.diffeomorph K).symm t) x).trans
      (parabolicSpacetimeHorizontal R.spacetime Q hQ a
        (E.toSpacetime ((P.diffeomorph K).symm t, x)))
  · intro t x v
    change (show SpacetimeModelVector n from
      ((G.spatialTangentEquiv ((P.diffeomorph K).symm t) x).trans
        (parabolicSpacetimeHorizontal R.spacetime Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x))) v).val) =
      mfderiv (𝓡 n) (spacetimeModel n)
        (fun y : C ↦ E.toSpacetime ((P.diffeomorph K).symm t, y)) x v
    change (show SpacetimeModelVector n from
      (parabolicSpacetimeHorizontal R.spacetime Q hQ a
        (E.toSpacetime ((P.diffeomorph K).symm t, x))
        ((G.spatialTangentEquiv ((P.diffeomorph K).symm t) x) v)).val) = _
    rw [parabolicSpacetimeHorizontal_val]
    exact G.spatialTangentEquiv_eq ((P.diffeomorph K).symm t) x v
  · intro t x v w
    change (scaleSmoothMetric (G.metric (parabolicTimeInv Q a (t : ℝ))) Q hQ).inner
        x v w =
      (parabolicSpacetime R.spacetime Q hQ a).horizontalMetric.inner
        (E.toSpacetime ((P.diffeomorph K).symm t, x))
        (parabolicSpacetimeHorizontal R.spacetime Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x))
          ((G.spatialTangentEquiv ((P.diffeomorph K).symm t) x) v))
        (parabolicSpacetimeHorizontal R.spacetime Q hQ a
          (E.toSpacetime ((P.diffeomorph K).symm t, x))
          ((G.spatialTangentEquiv ((P.diffeomorph K).symm t) x) w))
    rw [scaleSmoothMetric_inner, parabolicSpacetime_metric]
    exact congrArg (Q * ·) (G.metric_eq ((P.diffeomorph K).symm t) x v w)

noncomputable def unrescaledLabeling
    (L : SpacetimeSliceLabeling (atlasRescaling A Q hQ a).atlas) :
    SpacetimeSliceLabeling A := by
  let hQinv : 0 < (1 / Q : ℝ) := one_div_pos.mpr hQ
  refine {
    slice := fun t ↦ {
      carrier := (L.slice (parabolicTime Q a t)).carrier
      topologicalSpace := (L.slice (parabolicTime Q a t)).topologicalSpace
      chartedSpace := (L.slice (parabolicTime Q a t)).chartedSpace
      isManifold := (L.slice (parabolicTime Q a t)).isManifold
      measurableSpace := (L.slice (parabolicTime Q a t)).measurableSpace
      borelSpace := (L.slice (parabolicTime Q a t)).borelSpace
      metric := scaleSmoothMetric (L.slice (parabolicTime Q a t)).metric (1 / Q) hQinv
      toSpacetime := (L.slice (parabolicTime Q a t)).toSpacetime
      embedding := (L.slice (parabolicTime Q a t)).embedding
      time_eq := ?_
      range_eq := ?_ }
    boxMap := fun b t ht x ↦
      L.boxMap b (parabolicTime Q a t)
        ((parabolicTime_mem_parabolicInterval_iff Q hQ a (A.box b).interval t).2 ht) x
    boxMap_smooth := ?_
    boxMap_eq := ?_
    metric_eq := ?_ }
  · intro x
    have h := (L.slice (parabolicTime Q a t)).time_eq x
    change A.time ((L.slice (parabolicTime Q a t)).toSpacetime x) = t
    have htime : (atlasRescaling A Q hQ a).atlas.time
        ((L.slice (parabolicTime Q a t)).toSpacetime x) = parabolicTime Q a t := h
    change parabolicTime Q a
        (A.time ((L.slice (parabolicTime Q a t)).toSpacetime x)) = _ at htime
    have htime' := congrArg (parabolicTimeInv Q a) htime
    simpa only [parabolicTimeInv_parabolicTime Q hQ a] using htime'
  · ext p
    constructor
    · intro hp
      rcases hp with ⟨x, rfl⟩
      have htime := (L.slice (parabolicTime Q a t)).time_eq x
      change A.time ((L.slice (parabolicTime Q a t)).toSpacetime x) = t
      change parabolicTime Q a
          (A.time ((L.slice (parabolicTime Q a t)).toSpacetime x)) =
        parabolicTime Q a t at htime
      have htime' := congrArg (parabolicTimeInv Q a) htime
      simpa only [parabolicTimeInv_parabolicTime Q hQ a] using htime'
    · intro hp
      have hp' : (atlasRescaling A Q hQ a).atlas.time p = parabolicTime Q a t := by
        change parabolicTime Q a (A.time p) = _
        rw [hp]
      have hmem : p ∈ Set.range (L.slice (parabolicTime Q a t)).toSpacetime := by
        rw [(L.slice (parabolicTime Q a t)).range_eq]
        exact hp'
      exact hmem
  · intro b t ht
    exact L.boxMap_smooth b (parabolicTime Q a t)
      ((parabolicTime_mem_parabolicInterval_iff Q hQ a (A.box b).interval t).2 ht)
  · intro b t ht x
    have h := L.boxMap_eq b (parabolicTime Q a t)
      ((parabolicTime_mem_parabolicInterval_iff Q hQ a (A.box b).interval t).2 ht) x
    change (L.slice (parabolicTime Q a t)).toSpacetime
        (L.boxMap b (parabolicTime Q a t) _ x) = (A.box b).toSpacetime (⟨t, ht⟩, x)
    rw [h]
    exact (atlasRescaling A Q hQ a).box_map b ⟨t, ht⟩ x
  · intro b t ht x v w
    have h := L.metric_eq b (parabolicTime Q a t)
      ((parabolicTime_mem_parabolicInterval_iff Q hQ a (A.box b).interval t).2 ht) x v w
    change (scaleSmoothMetric (L.slice (parabolicTime Q a t)).metric (1 / Q) hQinv).inner
        _ _ _ = _
    rw [scaleSmoothMetric_inner, h]
    change (1 / Q : ℝ) *
        (((atlasRescaling A Q hQ a).atlas.box
          (cast (atlasRescaling A Q hQ a).box_index_eq.symm b)).metric
          (parabolicTime Q a t, (x : EuclideanSpace ℝ (Fin n))) v w) = _
    rw [(atlasRescaling A Q hQ a).metric_eq]
    field_simp [hQ.ne']
    rw [parabolicTimeInv_parabolicTime Q hQ a]

theorem rescaledLabelIdentification
    (L : SpacetimeSliceLabeling (atlasRescaling A Q hQ a).atlas) (t : ℝ) :
    Nonempty (SpacetimeSliceIdentification
      (parabolicSpacetime R.spacetime Q hQ a) (parabolicTime Q a t)
      (parabolicSpacetimeSlice R.spacetime R.slices Q hQ a (parabolicTime Q a t))
      (L.slice (parabolicTime Q a t))) := by
  cases (atlasRescaling A Q hQ a).time_eq
  obtain ⟨I⟩ := R.supplied_labels (unrescaledLabeling (A := A) (Q := Q) (hQ := hQ) (a := a) L) t
  dsimp [unrescaledLabeling] at I
  let g := parabolicSliceIdentification R.spacetime R.slices Q hQ a t
  let f := I.identification
  refine ⟨{
    identification := f.trans g
    identification_eq := ?_
    tangent_eq := ?_
    metric_eq := ?_
    measurable := ?_ }⟩
  · intro x
    change (g (f x)).val = (L.slice (parabolicTime Q a t)).toSpacetime x
    rw [parabolicSliceIdentification_val]
    exact I.identification_eq x
  · intro x v
    change (show SpacetimeModelVector n from
      ((parabolicSpacetimeSlice R.spacetime R.slices Q hQ a (parabolicTime Q a t)).tangentEquiv
        (g (f x)) (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x v)).val) = _
    rw [mfderiv_comp x (g.mdifferentiable (by simp) _) (f.mdifferentiable (by simp) _)]
    exact (parabolicSliceIdentification_tangent R.spacetime R.slices Q hQ a t
      (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)).trans (I.tangent_eq x v)
  · intro x v w
    change (parabolicSpacetimeSlice R.spacetime R.slices Q hQ a
      (parabolicTime Q a t)).metricOnPoints.inner
        (g (f x)) (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x v)
        (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x w) = _
    rw [mfderiv_comp x (g.mdifferentiable (by simp) _) (f.mdifferentiable (by simp) _)]
    have hg := parabolicSliceIdentification_metric R.spacetime R.slices Q hQ a t
      (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
    calc
      _ = Q * (R.slices t).metricOnPoints.inner (f x)
          (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) := hg
      _ = Q * (scaleSmoothMetric (L.slice (parabolicTime Q a t)).metric
          (1 / Q) (one_div_pos.mpr hQ)).inner x v w := congrArg (Q * ·) (I.metric_eq x v w)
      _ = (L.slice (parabolicTime Q a t)).metric.inner x v w := by
        rw [scaleSmoothMetric_inner]
        field_simp [hQ.ne']
  · constructor
    · exact g.continuous.measurable.comp I.measurable.1
    · exact I.measurable.2.comp g.symm.continuous.measurable

noncomputable def rescaledCarrierCore
    (hc : CompatibleSpacetimeTheory
      (parabolicSpacetime R.spacetime Q hQ a) R.timeIntervals)
    (hcc : CompatibleSpacetimeTheory.{u, 0}
      (parabolicSpacetime R.spacetime Q hQ a) R.timeIntervals) :
    GeneralizedFlowCarrierConclusion (atlasRescaling A Q hQ a).atlas := by
  cases (atlasRescaling A Q hQ a).box_index_eq
  let S := parabolicSpacetime R.spacetime Q hQ a
  let D : ∀ t : ℝ, SpacetimeSliceGeometry S t :=
    parabolicSpacetimeSlice R.spacetime R.slices Q hQ a
  let P := parabolicIntervalTransport R.timeIntervals Q hQ a
  refine {
    timeIntervals := R.timeIntervals
    interval_localDiffeomorph := R.interval_localDiffeomorph
    spacetime := S
    slices := D
    boxCylinder := fun b ↦ rescaledCylinder (R := R) (Q := Q) (hQ := hQ) (a := a) b
    boxCylinder_eq := ?_
    box_localDiffeomorph := ?_
    boxMetric := fun b ↦ transportedCylinderMetric (R := R) (Q := Q) (hQ := hQ) (a := a)
      (A.box b).interval (R.boxCylinder b) (R.boxMetric b)
    boxMetric_eq := ?_
    sliceBox := ?_
    sliceBox_eq := ?_
    sliceBox_localDiffeomorph := ?_
    sliceBox_metric := ?_
    supplied_labels := ?_
    horizontalBracket := ?_
    compatible := hc
    coordinate_compatible := hcc }
  · intro b p
    change (R.boxCylinder b).toSpacetime
        (((P.diffeomorph (A.box b).interval).symm p.1), p.2) =
      (A.box b).toSpacetime ((timeHomeomorph Q hQ a (A.box b).interval).symm p.1, p.2)
    rw [R.boxCylinder_eq]
    have htime : (P.diffeomorph (A.box b).interval).symm p.1 =
        (timeHomeomorph Q hQ a (A.box b).interval).symm p.1 := by
      apply Subtype.ext
      rw [P.inverse_eq]
      rfl
    rw [htime]
  · intro b p
    change IsLocalDiffeomorphAt (spacetimeModel n) (spacetimeModel n) ∞
      ((R.boxCylinder b).toSpacetime ∘
        ((P.diffeomorph (A.box b).interval).symm.prodCongr
          (Diffeomorph.refl (𝓡 n) (A.box b).spatial ∞))) p
    have hd := ((P.diffeomorph (A.box b).interval).symm.prodCongr
      (Diffeomorph.refl (𝓡 n) (A.box b).spatial ∞)).isLocalDiffeomorph p
    exact IsLocalDiffeomorphAt.comp
      (hf := hd) (hg := R.box_localDiffeomorph b _)
  · intro b t x v w
    change (scaleSmoothMetric ((R.boxMetric b).metric (parabolicTimeInv Q a (t : ℝ))) Q hQ).inner
        x v w = ((atlasRescaling A Q hQ a).atlas.box b).metric (t, x) v w
    rw [scaleSmoothMetric_inner]
    exact congrArg (Q * ·) (R.boxMetric_eq b
      ((P.diffeomorph (A.box b).interval).symm t) x v w)
  · intro b t ht x
    let t₀ : ℝ := parabolicTimeInv Q a t
    let ht₀ : t₀ ∈ (A.box b).interval.domain :=
      (mem_parabolicInterval_iff Q hQ a (A.box b).interval t).1 ht
    exact parabolicSliceIdentificationInv R.spacetime R.slices Q hQ a t
      (R.sliceBox b t₀ ht₀ x)
  · intro b t ht x
    let t₀ : ℝ := parabolicTimeInv Q a t
    let ht₀ : t₀ ∈ (A.box b).interval.domain :=
      (mem_parabolicInterval_iff Q hQ a (A.box b).interval t).1 ht
    have hslice := parabolicSliceIdentificationInv_val R.spacetime R.slices Q hQ a t
      (R.sliceBox b t₀ ht₀ x)
    have hbox := R.sliceBox_eq b t₀ ht₀ x
    change (parabolicSliceIdentificationInv R.spacetime R.slices Q hQ a t
      (R.sliceBox b t₀ ht₀ x)).val =
      (A.box b).toSpacetime
        ((timeHomeomorph Q hQ a (A.box b).interval).symm ⟨t, ht⟩, x)
    rw [hslice, hbox]
    congr 2
  · intro b t ht
    let t₀ : ℝ := parabolicTimeInv Q a t
    let ht₀ : t₀ ∈ (A.box b).interval.domain :=
      (mem_parabolicInterval_iff Q hQ a (A.box b).interval t).1 ht
    intro p
    let f := R.sliceBox b t₀ ht₀
    let g := parabolicSliceIdentificationInv R.spacetime R.slices Q hQ a t
    have hg := g.isLocalDiffeomorph (f p)
    exact IsLocalDiffeomorphAt.comp
      (hf := R.sliceBox_localDiffeomorph b t₀ ht₀ p) (hg := hg)
  · intro b t ht x v w
    let t₀ : ℝ := parabolicTimeInv Q a t
    let ht₀ : t₀ ∈ (A.box b).interval.domain :=
      (mem_parabolicInterval_iff Q hQ a (A.box b).interval t).1 ht
    let f := R.sliceBox b t₀ ht₀
    let g := parabolicSliceIdentificationInv R.spacetime R.slices Q hQ a t
    change (parabolicSpacetimeSlice R.spacetime R.slices Q hQ a t).metricOnPoints.inner
      (g (f x)) (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x v)
      (mfderiv (𝓡 n) (𝓡 n) (g ∘ f) x w) = _
    rw [mfderiv_comp x (g.mdifferentiable (by simp) _)
      ((R.sliceBox_localDiffeomorph b t₀ ht₀ x).mdifferentiableAt (by simp))]
    have hg := parabolicSliceIdentificationInv_metric R.spacetime R.slices Q hQ a t
      (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
    exact hg.trans (congrArg (Q * ·) (R.sliceBox_metric b t₀ ht₀ x v w))
  · intro L t
    dsimp [S, D]
    have htime : parabolicTime Q a (parabolicTimeInv Q a t) = t :=
      parabolicTime_parabolicTimeInv Q hQ a t
    have h := rescaledLabelIdentification (R := R) (Q := Q) (hQ := hQ) (a := a) L
      (parabolicTimeInv Q a t)
    rw [htime] at h
    exact h
  · intro U O hO hU p hp
    dsimp [S] at hU
    let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
        R.spacetime.Point := R.spacetime.chartedSpace
    let : IsManifold (spacetimeModel n) ∞ R.spacetime.Point := R.spacetime.isManifold
    let V : ∀ q : R.spacetime.Point, R.spacetime.Horizontal q := fun q ↦
      (parabolicSpacetimeHorizontal R.spacetime Q hQ a q).symm (U q)
    have hV : ContMDiffOn (spacetimeModel n)
        ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun q : R.spacetime.Point ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := R.spacetime.Horizontal) q (V q)) O :=
      (parabolicSpacetimeHorizontal_inverse_smooth R.spacetime Q hQ a).comp_contMDiffOn hU
    have hbracket := R.horizontalBracket V O hO hV p hp
    change mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : R.spacetime.Point ↦ parabolicTime Q a (R.spacetime.timeFunction q)) p
      (VectorField.mlieBracket (spacetimeModel n)
        ((1 / Q : ℝ) • R.spacetime.timeVector) (fun q ↦ (V q).val) p) = 0
    have hclock := parabolicClock_derivative R.spacetime Q a p
      (VectorField.mlieBracket (spacetimeModel n)
        ((1 / Q : ℝ) • R.spacetime.timeVector) (fun q ↦ (V q).val) p)
    calc
      _ = Q * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
          R.spacetime.timeFunction p
          (VectorField.mlieBracket (spacetimeModel n)
            ((1 / Q : ℝ) • R.spacetime.timeVector) (fun q ↦ (V q).val) p)) := hclock
      _ = Q * ((1 / Q) *
          (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
            R.spacetime.timeFunction p
            (VectorField.mlieBracket (spacetimeModel n) R.spacetime.timeVector
              (fun q ↦ (V q).val) p))) := by
        rw [VectorField.mlieBracket_const_smul_left
          (R.spacetime.timeVector_smooth.mdifferentiable (by simp) p), map_smul]
        simp only [smul_eq_mul]
      _ = 0 := by
        have hbracket' :
            (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
              R.spacetime.timeFunction p
              (VectorField.mlieBracket (spacetimeModel n) R.spacetime.timeVector
                (fun q ↦ (V q).val) p)) = 0 := hbracket
        rw [hbracket']
        field_simp [hQ.ne']

end PoincareConjecture.ParabolicRescaling
