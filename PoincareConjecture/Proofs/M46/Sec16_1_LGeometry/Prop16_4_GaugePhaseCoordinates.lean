import PoincareConjecture.Proofs.M14.Sec6_4_GaugeFieldRegularity
import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetConnection
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import PoincareConjecture.Definitions.M14GeneralizedLGeometry










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)





theorem exists_continuous_gaugeVelocity_coordinates {U : Set G.Point}
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hrec : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q) :
    ∃ v : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal → EuclideanSpace ℝ (Fin n),
      ContinuousOn v {z | z.proj ∈ U} ∧
      ∀ z, z.proj ∈ U →
        HEq z.2 ((G.gaugeCover.metric b).spatialTangentEquiv
          (lift z.proj).1 (lift z.proj).2 (v z)) := by
  classical
  let S : Set (TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal) := {z | z.proj ∈ U}
  let beta := fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => lift z.proj
  let v := fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
    ((G.gaugeCover.metric b).spatialTangentEquiv (beta z).1 (beta z).2).symm
      (if hz : z.proj ∈ U then (hrec z.proj hz).symm ▸ z.2 else 0)
  have hfield (z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal)
      (hz : z ∈ S) :
      HEq z.2 ((G.gaugeCover.metric b).spatialTangentEquiv (beta z).1 (beta z).2 (v z)) := by
    change z.proj ∈ U at hz
    dsimp only [v]
    rw [ContinuousLinearEquiv.apply_symm_apply, dif_pos hz]
    exact (eqRec_heq _ _).symm
  have hbeta : ContMDiffOn ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (spacetimeModel n) ∞ beta S :=
    hlift.comp (Bundle.contMDiff_proj G.Horizontal).contMDiffOn (fun _ hz => hz)
  let Y := fun z => (G.gaugeCover.metric b).spatialTangentEquiv (beta z).1 (beta z).2 (v z)
  have hY : ContMDiffOn ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        ((G.gaugeCover.cylinder b).toSpacetime (beta z)) (Y z)) S :=
    contMDiffOn_id.congr (fun z hz => TotalSpace.ext (hrec z.proj hz) (hfield z hz).symm)
  have hv : ContMDiffOn ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓡 n) ∞ v S := by
    intro z hz
    have hp := M14.movingGauge_horizontalField_pullback_contMDiffWithinAt
      (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
      (G.gaugeCover.metric b).toMovingSpacetimeGaugeGeometry (hbeta z hz) (hY z hz)
    have hi := (G.gaugeCover.spatial b).tangentBundle_snd_contMDiff
    have hc := hi.contMDiffAt.comp_contMDiffWithinAt z hp
    apply hc.congr
    · intro w _
      exact (((G.gaugeCover.metric b).spatialTangentEquiv (beta w).1 (beta w).2).symm_apply_apply
        (v w)).symm
    · exact (((G.gaugeCover.metric b).spatialTangentEquiv (beta z).1 (beta z).2).symm_apply_apply
        (v z)).symm
  exact ⟨v, hv.continuousOn, hfield⟩




theorem gaugeMomentum_coordinates_continuousOn
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    {U : Set G.Point}
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (v : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal → EuclideanSpace ℝ (Fin n))
    (hv : ContinuousOn v {z | z.proj ∈ U}) (T : ℝ) (x₀ : G.gaugeCover.spatial b)
    {C : Set ℝ} (htime : ∀ s ∈ C, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ContinuousOn (fun z : ℝ × TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
      ((lift z.2.proj).2.val,
        M08.chartMetricOperator W.flow T x₀ (z.1, (lift z.2.proj).2.val) (v z.2)))
      (C ×ˢ {z | z.proj ∈ U}) := by
  have hq : ContinuousOn
      (fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => (lift z.proj).2.val)
      {z | z.proj ∈ U} :=
    continuous_subtype_val.comp_continuousOn
      ((hlift.continuousOn.comp (FiberBundle.continuous_proj _ _).continuousOn
        (fun _ hz => hz)).snd)
  have hm : ContDiffOn ℝ ∞ (M08.chartMetricOperator W.flow T x₀)
      (C ×ˢ (extChartAt (𝓡 n) x₀).target) := by
    unfold M08.chartMetricOperator InnerProductSpace.continuousLinearMapOfBilin
    exact contDiffOn_const.clm_comp (M08.chartActionMetric_closed_contDiffOn W.flow T x₀ htime)
  have htarget (q : G.Point) : (lift q).2.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have heq : extChartAt (𝓡 n) x₀ (lift q).2 = (lift q).2.val := by rw [extChartAt_coe]; rfl
    rw [← heq]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have hqs : ContinuousOn
      (fun z : ℝ × TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => (lift z.2.proj).2.val)
      (C ×ˢ {z | z.proj ∈ U}) :=
    hq.comp continuous_snd.continuousOn (fun _ hz => hz.2)
  have hvs : ContinuousOn
      (fun z : ℝ × TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => v z.2)
      (C ×ˢ {z | z.proj ∈ U}) :=
    hv.comp continuous_snd.continuousOn (fun _ hz => hz.2)
  exact hqs.prodMk ((hm.continuousOn.comp (continuous_fst.continuousOn.prodMk hqs)
    (fun z hz => ⟨hz.1, htarget z.2.proj⟩)).clm_apply hvs)

end PoincareConjecture.Proofs.M46
