import PoincareConjecture.Proofs.M14.Sec6_2_ChartPullbackExtension
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedExtensionGluing
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {Y : ∀ s, G.Horizontal (γ s)}

theorem exists_local_pullbackExtension_Icc {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.spacetime.Horizontal) (γ s) (Y s)) (Set.Icc a b))
    {s : ℝ} (hs : s ∈ Set.Icc a b) :
    ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧
      Nonempty (M14PullbackExtension G γ (Set.Icc a b ∩ U) Y) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal (γ s)
  have hnear : γ ⁻¹' e.baseSet ∈ 𝓝[Set.Icc a b] s :=
    (hγ s hs).preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal (γ s)))
  obtain ⟨N, hN, hchart⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnear
  obtain ⟨l, r, ⟨hls, hsr⟩, hlr⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  let l' := (l + s) / 2
  let r' := (s + r) / 2
  let c := max a l'
  let d := min b r'
  have hll : l < l' := by dsimp only [l']; linarith
  have hls' : l' < s := by dsimp only [l']; linarith
  have hsr' : s < r' := by dsimp only [r']; linarith
  have hrr : r' < r := by dsimp only [r']; linarith
  have hcd : c < d := max_lt
    (lt_min hab (hs.1.trans_lt hsr'))
    (lt_min (hls'.trans_le hs.2) (hls'.trans hsr'))
  have hsub : Set.Icc c d ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ t ∈ Set.Icc c d, γ t ∈ e.baseSet := by
    intro t ht
    exact hchart ⟨hlr ⟨hll.trans_le ((le_max_right _ _).trans ht.1),
      (ht.2.trans (min_le_right _ _)).trans_lt hrr⟩, hsub ht⟩
  let y := fun t => (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
    (E := G.spacetime.Horizontal) (γ t) (Y t))).2
  have hpair := e.contMDiffOn.comp (hY.mono hsub)
    (fun t ht => e.mem_source.mpr (hsrc t ht))
  have hy : ContDiffOn ℝ ∞ y (Set.Icc c d) :=
    ContMDiffOn.contDiffOn (fun t ht => (hpair t ht).snd)
  obtain ⟨g, hg, hgy⟩ := M08.exists_smooth_extension_Icc hcd y hy
  let U := Set.Ioo l' r'
  have hUsub : Set.Icc a b ∩ U ⊆ Set.Icc c d := fun _ ht =>
    ⟨max_le ht.1.1 ht.2.1.le, le_min ht.1.2 ht.2.2.le⟩
  refine ⟨U, isOpen_Ioo, ⟨hls', hsr'⟩,
    ⟨pullbackExtensionInChart e isOpen_univ (Set.subset_univ _) g hg.contDiffOn
      (fun t ht => hsrc t (hUsub ht)) ?_⟩⟩
  intro t ht
  rw [hgy (hUsub ht)]
  exact e.symm_apply_apply_mk (hsrc t (hUsub ht)) (Y t)

theorem exists_pullbackExtension_Icc {a b : ℝ} (hab : a < b)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.spacetime.Horizontal) (γ s) (Y s)) (Set.Icc a b)) :
    Nonempty (M14PullbackExtension G γ (Set.Icc a b) Y) := by
  have hγ := (FiberBundle.continuous_proj
    (EuclideanSpace ℝ (Fin n)) G.Horizontal).comp_continuousOn hY.continuousOn
  exact exists_pullbackExtension_of_closed_local isClosed_Icc hγ
    (fun _ hs => exists_local_pullbackExtension_Icc hab hγ hY hs)

end PoincareConjecture.M14
