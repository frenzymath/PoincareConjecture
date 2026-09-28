import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.SourceGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

noncomputable def originalNestedSpatialMap (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier → M :=
  (equivShrink M).symm ∘ S.nestedSpatialMap P j k

noncomputable def originalNestedSpatialInverse (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    M → (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier :=
  S.nestedSpatialInverse P j k ∘ equivShrink M

theorem originalNestedSpatialInverse_left (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    S.originalNestedSpatialInverse P j k (S.originalNestedSpatialMap P j k x) = x := by
  simpa only [originalNestedSpatialInverse, originalNestedSpatialMap, Function.comp_apply,
    Equiv.apply_symm_apply] using S.nestedSpatialInverse_left P j k hx

theorem originalNestedSpatialMap_contMDiffAt (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (S.originalNestedSpatialMap P j k) x := by
  exact (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm.contMDiff.contMDiffAt.comp x
    (S.nestedSpatialMap_contMDiffAt P j k hx)

theorem originalNestedSpatialInverse_contMDiffAt (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    {x : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.carrier}
    (hx : S.initialWindowIdentification P j x ∈
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (S.originalNestedSpatialInverse P j k)
      (S.originalNestedSpatialMap P j k x) := by
  have hs := S.nestedSpatialInverse_contMDiffAt P j k hx
  have he : equivShrink M (S.originalNestedSpatialMap P j k x) = S.nestedSpatialMap P j k x :=
    (equivShrink M).apply_symm_apply _
  rw [← he] at hs
  exact hs.comp _ (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).contMDiff.contMDiffAt

noncomputable def nestedAncientEmbedding (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    (hstage : S.initialWindowIdentification P j ''
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    AncientSpacetimeEmbedding
      (R := S.rescaling ((S.nestedWindowLimit P j).geometric_limit.subsequence k))
      (S.ancientWindowLimit P)
      (ancientM18TimeWindow j ×ˢ (S.nestedWindowLimit P 0).geometric_limit.exhaustion j) := by
  let f := S.originalNestedSpatialMap P j k
  let g := S.originalNestedSpatialInverse P j k
  have hleft : ∀ x ∈ (S.nestedWindowLimit P 0).geometric_limit.exhaustion j, g (f x) = x :=
    fun x hx => S.originalNestedSpatialInverse_left P j k (hstage (mem_image_of_mem _ hx))
  refine {
    toFun := fun p => (p.1, f p.2)
    time_preserving := fun _ _ => rfl
    injective_on := ?_
    inverse := fun p => (p.1, g p.2)
    left_inverse := ?_
    right_inverse := ?_
    smooth_on := ?_
    smooth_inverse_on := ?_ }
  · intro p hp q hq hpq
    have hs := congrArg Prod.snd hpq
    have hinv := congrArg g hs
    rw [hleft p.2 hp.2, hleft q.2 hq.2] at hinv
    exact Prod.ext (congrArg (fun z : ℝ × M => z.1) hpq) hinv
  · intro p hp
    exact Prod.ext rfl (hleft p.2 hp.2)
  · rintro _ ⟨p, hp, rfl⟩
    exact Prod.ext rfl (congrArg f (hleft p.2 hp.2))
  · have hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f
        ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) := by
      intro x hx
      exact (S.originalNestedSpatialMap_contMDiffAt P j k
        (hstage (mem_image_of_mem _ hx))).contMDiffWithinAt
    exact contMDiffOn_fst.prodMk (hf.comp contMDiffOn_snd (fun _ hp => hp.2))
  · have hg : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g
        (f '' (S.nestedWindowLimit P 0).geometric_limit.exhaustion j) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (S.originalNestedSpatialInverse_contMDiffAt P j k
        (hstage (mem_image_of_mem _ hx))).contMDiffWithinAt
    apply contMDiffOn_fst.prodMk
    apply hg.comp contMDiffOn_snd
    rintro _ ⟨p, hp, rfl⟩
    exact mem_image_of_mem f hp.2

theorem nestedAncientEmbedding_base (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ)
    (hstage : S.initialWindowIdentification P j ''
      ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
        (S.nestedWindowLimit P j).geometric_limit.exhaustion k) :
    (S.nestedAncientEmbedding P j k hstage).toFun (-1, (S.ancientWindowLimit P).base) =
      (-1, S.base ((S.nestedWindowLimit P j).geometric_limit.subsequence k)) := by
  change (-1, S.originalNestedSpatialMap P j k (S.ancientWindowLimit P).base) =
    (-1, S.base ((S.nestedWindowLimit P j).geometric_limit.subsequence k))
  refine Prod.ext rfl ?_
  change (equivShrink M).symm (S.nestedSpatialMap P j k
    (S.nestedWindowLimit P 0).geometric_limit.limitFlow.base) = _
  rw [S.nestedSpatialMap_base P j k, Equiv.symm_apply_apply]

end PoincareConjecture.AncientRescalingSequence
