import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.NeckTransfer.Record
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.LimitGeometry.Charts.ForwardComparison
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric

/-!
# Eventual strong necks with one source-ball bound

Morgan--Tian Claim 11.35, final transfer, printed p. 291. Compactness of
the closed model slab and actual time cofinality supply the spatial and
temporal domains required by the strong-neck record constructor. One
fixed normalized source ball contains every produced full neck carrier.
Reviewed derivation: `claim11_35-strong-neck-record.md`, section 5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

/-- Actual full-family convergence gives eventual strong necks on the
original selected sequence, with the entire carrier in one normalized
source ball chosen before the index. Definition 9.78, printed p. 232,
and the final transfer following Claim 11.35, printed p. 291. -/
theorem blowup_eventually_strongNecks_of_cylinderFamilyClose
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (Φ : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace G.limit.sliceCarrier.carrier ∞)
    (q : UnitTwoSphere) (hcenter : Φ (q, 0) = G.limit.base)
    {delta : ℝ} (hdelta : 0 < delta)
    (hclose : ∀ᶠ k in atTop, RoundCylinderFamilyClose delta (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback (G.embedding k) Φ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k in atTop,
      ∃ hI : Ioc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0,
      ∃ N : GeneralizedStrongNeck (S.flow (G.subsequence k))
          (S.base (G.subsequence k)).1 delta,
        N.center = (S.base (G.subsequence k)).2 ∧
        N.scale = S.scale (G.subsequence k) ^ (-1 / 2 : ℝ) ∧
        N.carrier = blowup_zeroSliceEmbedding G k ''
          (Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹)) ∧
        N.coordinate_map = blowup_zeroSliceEmbedding G k ∘ Φ ∧
        N.coordinate_inverse = Φ.symm ∘ (blowup_zeroSliceEmbedding G k).symm ∧
        N.central_sphere = (blowup_zeroSliceEmbedding G k ∘ Φ) ''
          (univ ×ˢ ({0} : Set ℝ)) ∧
        (∀ s (hs : s ∈ Ioc (-1 : ℝ) 0) y, y ∈ N.carrier →
          N.time_cylinder.pointMap s hs y =
            (G.embedding k).pointMap s (hI hs) ((blowup_zeroSliceEmbedding G k).symm y)) ∧
        N.carrier ⊆ S.baseBall (G.subsequence k) A := by
  let g := G.limit.flow.metric 0
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  have hcompact : IsCompact (Φ '' (univ ×ˢ Icc (-delta⁻¹) delta⁻¹)) :=
    (isCompact_univ.prod isCompact_Icc).image Φ.continuous
  obtain ⟨R, hR, hball⟩ := hcompact.isBounded.subset_ball_lt 0 G.limit.base
  rw [g.toMetricSpace_ball] at hball
  have hslab : Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) ⊆ g.ball G.limit.base R :=
    (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)).trans hball
  refine ⟨2 * R, mul_pos (by norm_num) hR, ?_⟩
  filter_upwards [blowup_eventually_zeroSliceEmbedding_image_ball G hR
    (by norm_num : (1 : ℝ) < 2),
    G.exhaustion.time_cofinal (Icc (-1 : ℝ) 0) isCompact_Icc hJI, hclose]
    with k hk htime hc
  have hspace : Φ '' (univ ×ˢ Ioo (-delta⁻¹) delta⁻¹) ⊆ G.exhaustion.space k := by
    rw [← blowup_zeroSliceEmbedding_source G k]
    exact hslab.trans hk.1
  have hI : Ioc (-1 : ℝ) 0 ⊆ Icc (-G.exhaustion.time k) 0 :=
    Ioc_subset_Icc_self.trans htime
  obtain ⟨N, hNcenter, hNscale, hNcarrier, hNcoordinate, hNinverse, hNsphere, hNpoint⟩ :=
    blowup_exists_strongNeck_of_cylinderFamilyClose G Φ q hcenter hdelta k hspace hI hc
  refine ⟨hI, N, hNcenter, hNscale, hNcarrier, hNcoordinate, hNinverse, hNsphere,
    hNpoint, ?_⟩
  rw [hNcarrier]
  exact (image_mono hslab).trans hk.2

end PoincareMT.M32
