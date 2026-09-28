import PoincareConjecture.Proofs.M14.Mathlib.TrivializationConnection
import PoincareConjecture.Proofs.M14.Mathlib.VectorGraphDerivative
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackMetric










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

variable (e : Trivialization (EuclideanSpace ℝ (Fin n))
    (TotalSpace.proj : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal → G.Point))
  [MemTrivializationAtlas e]



noncomputable def horizontalConnectionDifference (p : G.Point) :
    G.Horizontal p →L[ℝ] TangentSpace (spacetimeModel n) p →L[ℝ] G.Horizontal p :=
  ((rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise).mono
    (subset_univ e.baseSet)).difference e.isCovariantDerivativeOn_flatCovariantDerivative p



theorem pullbackExtension_coordinates_contMDiffAt
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (he : γ s ∈ e.baseSet) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓡 n) ∞
      (fun z : ℝ × G.Point => e.continuousLinearMapAt ℝ z.2 (E.extension z.1 z.2))
      (s, γ s) := by
  obtain ⟨U, hU, hgraph, hE⟩ := E.joint_smooth
  have hfield := (hE _ (hgraph s hs)).contMDiffAt (hU.mem_nhds (hgraph s hs))
  have hcoord := (e.contMDiffAt_iff (f := fun z : ℝ × G.Point =>
    TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) z.2
      (E.extension z.1 z.2)) (e.mem_source.mpr he)).mp hfield
  apply hcoord.2.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt (e.open_baseSet.mem_nhds he)] with z hz
  exact e.continuousLinearMapAt_apply_of_mem ℝ hz _

set_option maxHeartbeats 1000000 in




theorem horizontalCovariantDerivative_coordinates
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (he : γ s ∈ e.baseSet) (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    e.continuousLinearMapAt ℝ (γ s) (M14HorizontalCovariantDerivative G γ J Y E s) =
      derivWithin (fun r => e.continuousLinearMapAt ℝ (γ r) (Y r)) J s +
        e.continuousLinearMapAt ℝ (γ s)
          (horizontalConnectionDifference e (γ s) (Y s)
            (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (γ s)) :=
    (metric.toCore (γ s)).toNormedAddCommGroupOfTopology
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  let : InnerProductSpace ℝ (G.Horizontal (γ s)) :=
    .ofCoreOfTopology (metric.toCore (γ s))
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  have hparam := (e.continuousLinearMapAt ℝ (γ s)).hasFDerivAt.comp_hasDerivAt s
    hd.differentiableAt.hasDerivAt
  simp only [Function.comp_def] at hparam
  have hgraph := vector_graph_hasDerivWithinAt _
    ((pullbackExtension_coordinates_contMDiffAt e E hs he).mdifferentiableAt (by simp)) hγ hJ
  dsimp only [Prod.fst, Prod.snd] at hgraph
  rw [hparam.deriv] at hgraph
  have hagrees := hgraph.congr_of_mem (fun r hr => by rw [E.agrees r hr]) hs
  have hderiv := hagrees.derivWithin hJ
  have hEs := ((E.spatial_smooth s (γ s) (E.graph_mem s hs)).contMDiffAt
    (E.domain_open.mem_nhds (E.graph_mem s hs))).mdifferentiableAt (by simp)
  have hspace := e.covariantDerivative_eq_flat_add_difference
    ((rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise).mono
      (subset_univ e.baseSet)) he hEs
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))
  rw [hderiv]
  simp only [M14HorizontalCovariantDerivative, map_add]
  rw [hspace, map_add, e.continuousLinearMapAt_symmL he, E.agrees s hs]
  exact (add_assoc _ _ _).symm

end PoincareConjecture.M14
