import PoincareConjecture.Proofs.M15.Lemma8_7_CylinderRange










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15




theorem compatibleCylinder_exists_local_spatial_inverse
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e) (q : D.Point × C) :
    ∃ O : Set G.Point, IsOpen O ∧ e.toSpacetime q ∈ O ∧
      ∃ k : G.Point → C,
        ContMDiffOn (spacetimeModel n) (𝓡 n) ∞ k O ∧
        ∀ q' : D.Point × C, e.toSpacetime q' ∈ O →
          k (e.toSpacetime q') = q'.2 := by
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
  let eT := movingGaugeSliceMap e.toMovingSpacetimeGauge G.slices q.1
  let hfixed := movingGaugeSliceMap_localDiffeomorph e.toMovingSpacetimeGauge
    G.slices g.toMovingSpacetimeGaugeGeometry q.1 q.2
  let psi := hfixed.localInverse
  let gT : G.gaugeCover.spatial i → (G.slices q.1.val).Point :=
    fun c => ⟨e0.toSpacetime (z.1, c), (e0.time_eq _).trans hclock⟩
  have hgT : ContMDiff (𝓡 n) (𝓡 n) ∞ gT := by
    have h := (movingGaugeSliceMap_localDiffeomorph e0.toMovingSpacetimeGauge G.slices
      (G.gaugeCover.metric i).toMovingSpacetimeGaugeGeometry z.1).contMDiff
    have htransport (s : ℝ) (hs : z.1.val = s) :
        ContMDiff (𝓡 n) (𝓡 n) ∞
          (show G.gaugeCover.spatial i → (G.slices s).Point from
            fun c => ⟨e0.toSpacetime (z.1, c), (e0.time_eq _).trans hs⟩) := by
      subst s
      exact h
    exact htransport q.1.val hclock
  let j := fun p : G.Point => gT (phi p).2
  have hj : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞ j phi.source :=
    (hgT.comp contMDiff_snd).comp_contMDiffOn phi.contMDiffOn_toFun
  have hjbase : j (e.toSpacetime q) = eT q.2 := by
    dsimp only [j]
    rw [hbase]
    apply Subtype.ext
    exact hz
  let O1 := phi.source ∩ j ⁻¹' psi.source
  have hO1 : IsOpen O1 := hj.continuousOn.isOpen_inter_preimage
    phi.open_source psi.open_source
  have hpO1 : e.toSpacetime q ∈ O1 := by
    refine ⟨hp0, ?_⟩
    change j (e.toSpacetime q) ∈ psi.source
    rw [hjbase]
    exact hfixed.localInverse_mem_source
  have hk : ContMDiffOn (spacetimeModel n) (𝓡 n) ∞ (psi ∘ j) O1 :=
    psi.contMDiffOn_toFun.comp (hj.mono inter_subset_left) (fun _ hp => hp.2)
  obtain ⟨U, V, hU, hqU, hV, hqV, hprod⟩ := mem_nhds_prod_iff'.mp
    (e.embedding.continuous.continuousAt (phi.open_source.mem_nhds hp0))
  obtain ⟨delta, hdelta, hdeltaU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  have hrectangle (t : D.Point) (ht : |t.val - q.1.val| < delta)
      (c : C) (hc : c ∈ V) : e.toSpacetime (t, c) ∈ phi.source := by
    apply hprod
    exact ⟨hdeltaU (by simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ht), hc⟩
  let N := Metric.ball q.1 delta ×ˢ (V ∩ psi.target)
  have hN : IsOpen N := Metric.isOpen_ball.prod (hV.inter psi.open_target)
  have hqN : q ∈ N :=
    ⟨Metric.mem_ball_self hdelta, hqV, hfixed.localInverse_mem_target⟩
  obtain ⟨H, hH, hHN⟩ := e.embedding.isInducing.isOpen_iff.mp hN
  let O := H ∩ O1
  have hpH : e.toSpacetime q ∈ H := by
    change q ∈ e.toSpacetime ⁻¹' H
    rw [hHN]
    exact hqN
  refine ⟨O, hH.inter hO1, ⟨hpH, hpO1⟩, psi ∘ j,
    hk.mono inter_subset_right, ?_⟩
  intro q' hq'
  have hq'N : q' ∈ N := by
    rw [← hHN]
    exact hq'.1
  have hdeltaT : |q'.1.val - q.1.val| < delta := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hq'N.1
  have hc : q'.2 ∈ V := hq'N.2.1
  have hstart : e.toSpacetime (q.1, q'.2) ∈ phi.source :=
    hrectangle q.1 (by simpa only [sub_self, abs_zero] using hdelta) q'.2 hc
  have hconstant : (phi (e.toSpacetime (q.1, q'.2))).2 =
      (phi (e.toSpacetime q')).2 := by
    rcases le_total q.1.val q'.1.val with hle | hle
    · apply cylinder_localInverse_spatial_constant e0 z hlocal
        e.toCompatibleSpacetimeEmbedding q'.2 q.1 q'.1 hle
      intro s hlow hhigh
      apply hrectangle s ?_ q'.2 hc
      rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
      exact (sub_le_sub_right hhigh q.1.val).trans_lt
        ((le_abs_self (q'.1.val - q.1.val)).trans_lt hdeltaT)
    · symm
      apply cylinder_localInverse_spatial_constant e0 z hlocal
        e.toCompatibleSpacetimeEmbedding q'.2 q'.1 q.1 hle
      intro s hlow hhigh
      apply hrectangle s ?_ q'.2 hc
      rw [abs_of_nonpos (sub_nonpos.mpr hhigh)]
      have hbound := (neg_le_abs (q'.1.val - q.1.val)).trans_lt hdeltaT
      linarith
  have ht : (phi (e.toSpacetime (q.1, q'.2))).1 = z.1 := by
    apply Subtype.ext
    rw [← e0.time_eq (phi (e.toSpacetime (q.1, q'.2))),
      hlocal.localInverse_right_inv hstart, e.time_eq, hclock]
  have hjq' : j (e.toSpacetime q') = eT q'.2 := by
    apply Subtype.ext
    change e0.toSpacetime (z.1, (phi (e.toSpacetime q')).2) = e.toSpacetime (q.1, q'.2)
    rw [← hconstant, ← ht]
    exact hlocal.localInverse_right_inv hstart
  change psi (j (e.toSpacetime q')) = q'.2
  rw [hjq']
  exact hfixed.localInverse_left_inv hq'N.2.2

end PoincareConjecture.Proofs.M15
