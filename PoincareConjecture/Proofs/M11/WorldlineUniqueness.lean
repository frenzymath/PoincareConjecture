import PoincareConjecture.Proofs.M11.BoxWorldline
import PoincareConjecture.Proofs.M11.IntervalNeighborhood
import Mathlib.Topology.Connected.Clopen





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]

theorem worldline_unique_same_interval (A : AdaptedMetricAtlas n X) (K : SpacetimeInterval)
    (γ η : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval K))
    (s : (smoothInterval K).Point) (hs : γ.curve s = η.curve s)
    (t : (smoothInterval K).Point) : γ.curve t = η.curve t := by
  let := intervalChartedSpace K
  let := adaptedChartedSpace A
  let E : Set (smoothInterval K).Point := {r | γ.curve r = η.curve r}
  have hclosed : IsClosed E := isClosed_eq γ.smooth.continuous η.smooth.continuous
  have hopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro r hr
    obtain ⟨b, hb⟩ := box_targets_cover A (γ.curve r)
    let e := boxHomeomorph (A.box b)
    have hη : η.curve r ∈ e.target := hr ▸ hb
    let U : Set (smoothInterval K).Point := γ.curve ⁻¹' e.target ∩ η.curve ⁻¹' e.target
    have hU : U ∈ 𝓝 r := ((e.open_target.preimage γ.smooth.continuous).inter
      (e.open_target.preimage η.smooth.continuous)).mem_nhds ⟨hb, hη⟩
    obtain ⟨J, hJ, hrJ, hJn, hJU⟩ := interval_exists_small_neighborhood K r hU
    let γ' := worldlineTimeRestrict intervalSystem K J hJ γ
    let η' := worldlineTimeRestrict intervalSystem K J hJ η
    have hγ' (q : (smoothInterval J).Point) : γ'.curve q ∈ e.target := (hJU q).1
    have hη' (q : (smoothInterval J).Point) : η'.curve q ∈ e.target := (hJU q).2
    apply Filter.mem_of_superset hJn
    intro q hq
    have hγq : γ.curve q ∈ e.target := hγ' ⟨q.val, hq⟩
    have hηq : η.curve q ∈ e.target := hη' ⟨q.val, hq⟩
    have hspace : (e.symm (γ.curve q)).2 = (e.symm (η.curve q)).2 := by
      calc
        _ = (e.symm (γ.curve r)).2 :=
          worldline_box_spatial_constant A J γ' b hγ' ⟨q.val, hq⟩ ⟨r.val, hrJ⟩
        _ = (e.symm (η.curve r)).2 := congrArg (fun p ↦ (e.symm p).2) hr
        _ = (e.symm (η.curve q)).2 :=
          worldline_box_spatial_constant A J η' b hη' ⟨r.val, hrJ⟩ ⟨q.val, hq⟩
    apply e.symm.injOn hγq hηq
    apply Prod.ext _ hspace
    apply Subtype.ext
    calc
      _ = A.time (γ.curve q) := boxHomeomorph_inverse_time (A.box b) hγq
      _ = q.val := γ.time_eq q
      _ = A.time (η.curve q) := (η.time_eq q).symm
      _ = _ := (boxHomeomorph_inverse_time (A.box b) hηq).symm
  let : PreconnectedSpace (smoothInterval K).Point :=
    isPreconnected_iff_preconnectedSpace.mp (interval_convex K).isPreconnected
  have hE : E = univ := (show IsClopen E from ⟨hclosed, hopen⟩).eq_univ ⟨s, hs⟩
  have ht : t ∈ E := hE.symm ▸ mem_univ t
  exact ht

theorem adapted_worldline_unique (A : AdaptedMetricAtlas n X) (K L : SpacetimeInterval)
    (γ : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval K))
    (η : SpacetimeWorldline (adaptedSpacetime A) (smoothInterval L))
    (s : ℝ) (hsK : s ∈ K.domain) (hsL : s ∈ L.domain)
    (hs : γ.curve ⟨s, hsK⟩ = η.curve ⟨s, hsL⟩)
    (t : ℝ) (htK : t ∈ K.domain) (htL : t ∈ L.domain) :
    γ.curve ⟨t, htK⟩ = η.curve ⟨t, htL⟩ := by
  by_cases hn : (K.domain ∩ L.domain).Nontrivial
  · let J : SpacetimeInterval := ⟨K.domain ∩ L.domain, K.ordConnected.inter L.ordConnected, hn⟩
    exact worldline_unique_same_interval A J
      (worldlineTimeRestrict intervalSystem K J inter_subset_left γ)
      (worldlineTimeRestrict intervalSystem L J inter_subset_right η)
      ⟨s, hsK, hsL⟩ hs ⟨t, htK, htL⟩
  · have hts : t = s := (Set.not_nontrivial_iff.mp hn) ⟨htK, htL⟩ ⟨hsK, hsL⟩
    subst t
    exact hs

theorem adapted_embedding_unique (A : AdaptedMetricAtlas n X)
    {C : Type*} [TopologicalSpace C] (K L : SpacetimeInterval)
    (e : CompatibleSpacetimeEmbedding (adaptedSpacetime A) (smoothInterval K) C)
    (f : CompatibleSpacetimeEmbedding (adaptedSpacetime A) (smoothInterval L) C)
    (s : ℝ) (hsK : s ∈ K.domain) (hsL : s ∈ L.domain) (source : C → X)
    (he : e.IsBasedAt ⟨s, hsK⟩ source) (hf : f.IsBasedAt ⟨s, hsL⟩ source)
    (t : ℝ) (htK : t ∈ K.domain) (htL : t ∈ L.domain) (x : C) :
    e.toSpacetime (⟨t, htK⟩, x) = f.toSpacetime (⟨t, htL⟩, x) :=
  adapted_worldline_unique A K L (embeddingWorldline e x) (embeddingWorldline f x)
    s hsK hsL ((he x).trans (hf x).symm) t htK htL

end PoincareConjecture.Proofs.M11
