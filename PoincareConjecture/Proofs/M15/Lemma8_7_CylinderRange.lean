import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceMap
import PoincareConjecture.Definitions.M14GeneralizedLGeometry
import PoincareConjecture.Proofs.M15.Lemma8_7_CylinderCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15

theorem compatibleCylinder_range_mem_nhdsWithin_timeDomain
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e)
    (q : D.Point × C) :
    Set.range e.toSpacetime ∈
      𝓝[{p : G.Point | G.spacetime.timeFunction p ∈ K.domain}]
        (e.toSpacetime q) := by
  obtain ⟨i, z, hz⟩ := G.gaugeCover.covers (e.toSpacetime q)
  let e0 := G.gaugeCover.cylinder i
  let hlocal := G.gaugeCover.local_diffeomorph i z
  let phi := hlocal.localInverse
  have hp0 : e.toSpacetime q ∈ phi.source := by
    rw [← hz]
    exact hlocal.localInverse_mem_source
  have hbase : phi (e.toSpacetime q) = z := by
    rw [← hz]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hclock : z.1.val = q.1.val := by
    rw [← e0.time_eq z, ← e.time_eq q]
    exact congrArg G.spacetime.timeFunction hz
  obtain ⟨A, V0, hA, hzA, hV0, hzV0, hrect⟩ :=
    mem_nhds_prod_iff'.mp (phi.open_target.mem_nhds hlocal.localInverse_mem_target)
  let O1 := phi.source ∩ phi ⁻¹' (A ×ˢ V0)
  have hO1 : IsOpen O1 := phi.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
    phi.open_source (hA.prod hV0)
  have hpO1 : e.toSpacetime q ∈ O1 := by
    refine ⟨hp0, ?_⟩
    change phi (e.toSpacetime q) ∈ A ×ˢ V0
    rw [hbase]
    exact ⟨hzA, hzV0⟩
  obtain ⟨U, V, hU, hqU, hV, hqV, hprod⟩ := mem_nhds_prod_iff'.mp
    (e.embedding.continuous.continuousAt (hO1.mem_nhds hpO1))
  obtain ⟨delta, hdelta, hdeltaU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  have hrectangle (t : D.Point) (ht : |t.val - q.1.val| < delta)
      (c : C) (hc : c ∈ V) : e.toSpacetime (t, c) ∈ O1 := by
    apply hprod
    exact ⟨hdeltaU (by simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ht), hc⟩
  let eT := movingGaugeSliceMap e.toMovingSpacetimeGauge G.slices q.1
  let gT : G.gaugeCover.spatial i → (G.slices q.1.val).Point :=
    fun c => ⟨e0.toSpacetime (z.1, c), (e0.time_eq _).trans hclock⟩
  have heTopen : IsOpen (eT '' V) :=
    (movingGaugeSliceMap_localDiffeomorph e.toMovingSpacetimeGauge G.slices
      g.toMovingSpacetimeGaugeGeometry q.1).isOpenMap V hV
  have hgT : Continuous gT :=
    (e0.embedding.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  let W := V0 ∩ gT ⁻¹' (eT '' V)
  have hW : IsOpen W := hV0.inter (heTopen.preimage hgT)
  have hzW : z.2 ∈ W := by
    refine ⟨hzV0, q.2, hqV, ?_⟩
    apply Subtype.ext
    exact hz.symm
  let O2 := phi.source ∩ (fun p : G.Point => (phi p).2) ⁻¹' W
  have hO2 : IsOpen O2 :=
    (continuous_snd.comp_continuousOn phi.contMDiffOn_toFun.continuousOn).isOpen_inter_preimage
      phi.open_source hW
  have hpO2 : e.toSpacetime q ∈ O2 := by
    refine ⟨hp0, ?_⟩
    change (phi (e.toSpacetime q)).2 ∈ W
    rwa [hbase]
  let O := O1 ∩ O2 ∩ {p : G.Point | |G.spacetime.timeFunction p - q.1.val| < delta}
  have htimeCont : Continuous G.spacetime.timeFunction :=
    (show ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction from
      G.spacetime.time_smooth).continuous
  have hO : IsOpen O := (hO1.inter hO2).inter
    (isOpen_lt ((htimeCont.sub continuous_const).abs) continuous_const)
  have hpO : e.toSpacetime q ∈ O := by
    refine ⟨⟨hpO1, hpO2⟩, ?_⟩
    change |G.spacetime.timeFunction (e.toSpacetime q) - q.1.val| < delta
    simpa only [e.time_eq, sub_self, abs_zero] using hdelta
  apply mem_of_superset (inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hpO))
    self_mem_nhdsWithin)
  rintro p ⟨hp, htK⟩
  have hpPhi : p ∈ phi.source := hp.1.1.1
  have hpW : (phi p).2 ∈ W := hp.1.2.2
  obtain ⟨c, hc, hmatch⟩ := hpW.2
  let t : D.Point := ⟨G.spacetime.timeFunction p, htK⟩
  have hdeltaT : |t.val - q.1.val| < delta := hp.2
  have hend : e.toSpacetime (t, c) ∈ O1 := hrectangle t hdeltaT c hc
  have hfixed : (z.1, (phi p).2) ∈ phi.target := hrect ⟨hzA, hpW.1⟩
  have hfixedEq : phi (e.toSpacetime (q.1, c)) = (z.1, (phi p).2) := by
    have hm : e.toSpacetime (q.1, c) = e0.toSpacetime (z.1, (phi p).2) :=
      congrArg (fun w : (G.slices q.1.val).Point => w.val) hmatch
    rw [hm]
    exact hlocal.localInverse_left_inv hfixed
  have hconstant : (phi (e.toSpacetime (q.1, c))).2 =
      (phi (e.toSpacetime (t, c))).2 := by
    rcases le_total q.1.val t.val with hle | hle
    · apply cylinder_localInverse_spatial_constant e0 z hlocal
        e.toCompatibleSpacetimeEmbedding c q.1 t hle
      intro s hlow hhigh
      apply (hrectangle s ?_ c hc).1
      rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
      exact (sub_le_sub_right hhigh q.1.val).trans_lt
        ((le_abs_self (t.val - q.1.val)).trans_lt hdeltaT)
    · symm
      apply cylinder_localInverse_spatial_constant e0 z hlocal
        e.toCompatibleSpacetimeEmbedding c t q.1 hle
      intro s hlow hhigh
      apply (hrectangle s ?_ c hc).1
      rw [abs_of_nonpos (sub_nonpos.mpr hhigh)]
      have hbound := (neg_le_abs (t.val - q.1.val)).trans_lt hdeltaT
      linarith
  have hspatial : (phi (e.toSpacetime (t, c))).2 = (phi p).2 := by
    rw [hfixedEq] at hconstant
    exact hconstant.symm
  have htime (w : G.Point) (hw : w ∈ phi.source) :
      (phi w).1.val = G.spacetime.timeFunction w := by
    rw [← e0.time_eq (phi w), hlocal.localInverse_right_inv hw]
  have hinverse : phi (e.toSpacetime (t, c)) = phi p := by
    apply Prod.ext
    · apply Subtype.ext
      rw [htime _ hend.1, htime _ hpPhi, e.time_eq]
    · exact hspatial
  refine ⟨(t, c), ?_⟩
  exact (hlocal.localInverse_right_inv hend.1).symm.trans
    ((congrArg e0.toSpacetime hinverse).trans (hlocal.localInverse_right_inv hpPhi))

end PoincareConjecture.Proofs.M15
