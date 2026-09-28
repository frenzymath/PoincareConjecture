import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CornerPrimitive
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePrimitivePartition
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeOverlapPartition










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem attainmentGauge_spatial_contDiffOn (e : AttainmentGauge G)
    {gamma : ℝ → G.Point} {J : Set ℝ}
    (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma J)
    (hsource : MapsTo gamma J e.source) :
    ContDiffOn ℝ 1 (fun s => (e.lift (gamma s)).2.val) J := by
  have hpair := (e.smooth.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp hgamma hsource
  have hspatial : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) 1
      (fun s => (e.lift (gamma s)).2) J := fun s hs => (hpair s hs).snd
  have hval : ContMDiff (𝓡 3) (𝓡 3) 1
      (Subtype.val : G.gaugeCover.spatial e.index → EuclideanSpace ℝ (Fin 3)) :=
    contMDiff_subtype_val
  exact (hval.comp_contMDiffOn hspatial).contDiffOn




theorem oneCorner_gauge_primitive_partition {a c b : ℝ}
    (hab : a < b) (_hac : a ≤ c) (_hcb : c ≤ b)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hleft : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc a c))
    (hright : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) 1 gamma (Icc c b)) :
    ∃ R : GaugePrimitivePartition gamma a b,
      ∀ i, (R.velocity i : ℝ → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Icc (R.node i.castSucc) (R.node i.succ))]
          deriv (fun s => ((R.gauge i).lift (gamma s)).2.val) := by
  classical
  have hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn (fun _ : ℕ => gamma) gamma atTop (Icc a b) := by
    let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
      ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
    let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
    change TendstoUniformlyOn (fun _ : ℕ => gamma) gamma atTop (Icc a b)
    intro U hU
    exact Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hU)
  obtain ⟨m, t, e, l, r, K, N, _, ht, hta, htb, hp, _⟩ :=
    exists_compact_overlapping_gauge_partition hab gamma hgamma (fun _ : ℕ => gamma) hlim
  have hbig (i : Fin m) : Icc (l i) (r i) ⊆ Icc a b :=
    Icc_subset_Icc (hp i).1 (hp i).2.2.1
  have hcore (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (l i) (r i) :=
    Icc_subset_Icc (hp i).2.2.2.1 (hp i).2.2.2.2.1
  have hsrc (i : Fin m) : MapsTo gamma (Icc (l i) (r i)) (e i).source := by
    intro s hs
    exact (hp i).2.2.2.2.2.2.2.1 (interior_subset
      ((hp i).2.2.2.2.2.2.1 (mem_image_of_mem gamma hs)))
  have hprimitive (i : Fin m) :
      ∃ v : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (t i.castSucc) (t i.succ),
        (v : ℝ → EuclideanSpace ℝ (Fin 3))
          =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
            deriv (fun s => ((e i).lift (gamma s)).2.val) ∧
        ∀ s ∈ Icc (t i.castSucc) (t i.succ),
          ((e i).lift (gamma s)).2.val = ((e i).lift (gamma (t i.castSucc))).2.val +
            ∫ z in t i.castSucc..s, v z := by
    apply oneCorner_chartL2_primitive_on (c := c) (ht (Fin.castSucc_le_succ i))
    · apply attainmentGauge_spatial_contDiffOn (e i)
      · exact hleft.mono (fun _ hs => ⟨(hbig i (hcore i hs.1)).1, hs.2⟩)
      · exact fun _ hs => hsrc i (hcore i hs.1)
    · apply attainmentGauge_spatial_contDiffOn (e i)
      · exact hright.mono (fun _ hs => ⟨hs.2, (hbig i (hcore i hs.1)).2⟩)
      · exact fun _ hs => hsrc i (hcore i hs.1)
  choose v hv hprim using hprimitive
  let R : GaugePrimitivePartition gamma a b := {
    count := m
    node := t
    monotone := ht
    first := hta
    last := htb
    gauge := e
    left := l
    right := r
    big_subset := hbig
    core_subset := hcore
    near := fun i => (hp i).2.2.2.2.2.2.2.2
    source := hsrc
    velocity := v
    primitive := hprim }
  exact ⟨R, hv⟩

end PoincareConjecture.Proofs.M46
