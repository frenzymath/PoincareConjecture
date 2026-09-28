import PoincareConjecture.Definitions.M14PathCalculus










set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J K : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}



def pullbackExtensionRestrict (E : M14PullbackExtension G γ J Y) (hK : K ⊆ J) :
    M14PullbackExtension G γ K Y where
  extension := E.extension
  domain := E.domain
  domain_open := E.domain_open
  graph_mem s hs := E.graph_mem s (hK hs)
  spatial_smooth := E.spatial_smooth
  joint_smooth := by
    obtain ⟨U, hU, hgraph, hE⟩ := E.joint_smooth
    exact ⟨U, hU, fun s hs => hgraph s (hK hs), hE⟩
  agrees s hs := E.agrees s (hK hs)
  parameter_derivative s hs := E.parameter_derivative s (hK hs)



theorem horizontalCovariantDerivative_restrict (E : M14PullbackExtension G γ J Y)
    (hK : K ⊆ J) {s : ℝ} (hs : K ∈ 𝓝 s) :
    M14HorizontalCovariantDerivative G γ J Y E s =
      M14HorizontalCovariantDerivative G γ K Y (pullbackExtensionRestrict E hK) s := by
  unfold M14HorizontalCovariantDerivative
  rw [mfderivWithin_of_mem_nhds (mem_of_superset hs hK), mfderivWithin_of_mem_nhds hs]
  rfl




theorem horizontalCovariantDerivative_restrict_inter (E : M14PullbackExtension G γ J Y)
    {s : ℝ} (hK : K ∈ 𝓝 s) :
    M14HorizontalCovariantDerivative G γ J Y E s =
      M14HorizontalCovariantDerivative G γ (J ∩ K) Y
        (pullbackExtensionRestrict E inter_subset_left) s := by
  unfold M14HorizontalCovariantDerivative
  rw [mfderivWithin_inter hK]
  rfl





theorem horizontalCovariantDerivative_restrict_subset (E : M14PullbackExtension G γ J Y)
    (hK : K ⊆ J) {s : ℝ} (hKs : UniqueDiffWithinAt ℝ K s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    M14HorizontalCovariantDerivative G γ J Y E s =
      M14HorizontalCovariantDerivative G γ K Y (pullbackExtensionRestrict E hK) s := by
  unfold M14HorizontalCovariantDerivative
  rw [mfderivWithin_subset hK hKs.uniqueMDiffWithinAt hγ]
  rfl

end PoincareConjecture.M14
