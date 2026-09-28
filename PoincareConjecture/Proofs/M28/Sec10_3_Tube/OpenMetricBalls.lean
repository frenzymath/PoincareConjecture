import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CompactConfinement











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem intrinsicOpenMetric_ball_eq_preimage (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (p : V) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (V : Set M)) :
    (intrinsicOpenMetric g V).ball p r =
      (Subtype.val : V → M) ⁻¹' g.ball (p : M) r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ext q
  change (intrinsicOpenMetric g V).edist p q < ENNReal.ofReal r ↔
    g.edist (p : M) (q : M) < ENNReal.ofReal r
  rw [intrinsicOpenMetric_edist g V]
  constructor
  · intro hq
    have hle : g.edist (p : M) (q : M) ≤
        intrinsicEDist g (V : Set M) (p : M) (q : M) := by
      rw [intrinsicEDist]
      apply le_sInf
      rintro L ⟨α, hα, hα0, hα1, _, rfl⟩
      exact Manifold.riemannianEDist_le_pathELength hα hα0 hα1 zero_le_one
    exact hle.trans_lt hq
  · intro hq
    obtain ⟨α, hα0, hα1, hα, hαlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hq
    have hαball : MapsTo α (Icc (0 : ℝ) 1) (g.ball (p : M) r) := by
      simpa only [hα0] using g.mapsTo_ball_of_pathELength_lt hα hαlen
    have hinf := intrinsicEDist_le_pathELength g zero_le_one hα
      (fun t ht => hball (hαball ht))
    rw [hα0, hα1] at hinf
    exact hinf.trans_lt hαlen



theorem intrinsicOpenMetric_closure_ball_eq_preimage (g : RiemannianMetric 3 M)
    (V : TopologicalSpace.Opens M) (p : V) {r : ℝ}
    (hball : g.ball (p : M) r ⊆ (V : Set M)) :
    closure ((intrinsicOpenMetric g V).ball p r) =
      (Subtype.val : V → M) ⁻¹' closure (g.ball (p : M) r) := by
  rw [intrinsicOpenMetric_ball_eq_preimage g V p hball]
  have hopen := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  exact (hopen.preimage_closure_eq_closure_preimage continuous_subtype_val _).symm

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]




theorem CapCertificate.core_ball_intrinsicOpenMetric
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (V : TopologicalSpace.Opens M) (hNV : N.carrier ⊆ (V : Set M))
    (y : V) (hy : (y : M) ∈ N.core) :
    (intrinsicOpenMetric g V).ball y (N.core_radius y) =
        (Subtype.val : V → M) ⁻¹' g.ball (y : M) (N.core_radius y) ∧
      closure ((intrinsicOpenMetric g V).ball y (N.core_radius y)) =
        (Subtype.val : V → M) ⁻¹' closure (g.ball (y : M) (N.core_radius y)) ∧
      IsCompact (closure ((intrinsicOpenMetric g V).ball y (N.core_radius y))) ∧
      closure ((intrinsicOpenMetric g V).ball y (N.core_radius y)) ⊆
        (Subtype.val : V → M) ⁻¹' N.carrier := by
  have hclosure : closure (g.ball (y : M) (N.core_radius y)) ⊆ (V : Set M) :=
    (N.core_ball_subset y hy).trans hNV
  have hball : g.ball (y : M) (N.core_radius y) ⊆ (V : Set M) :=
    subset_closure.trans hclosure
  have hclosure_eq := intrinsicOpenMetric_closure_ball_eq_preimage g V y hball
  refine ⟨intrinsicOpenMetric_ball_eq_preimage g V y hball, hclosure_eq, ?_, ?_⟩
  · rw [hclosure_eq]
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (N.core_ball_compact y hy)
    intro z hz
    exact ⟨⟨z, hclosure hz⟩, rfl⟩
  · rw [hclosure_eq]
    exact preimage_mono (N.core_ball_subset y hy)

end PoincareConjecture.M28
