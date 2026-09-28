import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Proofs.M08.SmoothEndpointExtension

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {Y : ∀ s, G.Horizontal (γ s)}

noncomputable def pullbackExtensionInChart
    (e : Bundle.Trivialization (EuclideanSpace ℝ (Fin n))
      (Bundle.TotalSpace.proj : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
        G.Horizontal → G.Point)) [MemTrivializationAtlas e]
    {J U : Set ℝ} (hU : IsOpen U) (hJU : J ⊆ U)
    (y : ℝ → EuclideanSpace ℝ (Fin n)) (hy : ContDiffOn ℝ ∞ y U)
    (hγ : ∀ s ∈ J, γ s ∈ e.baseSet)
    (hY : ∀ s ∈ J, e.symm (γ s) (y s) = Y s) :
    M14PullbackExtension G γ J Y where
  extension r p := e.symm p (y r)
  domain := e.baseSet
  domain_open := e.open_baseSet
  graph_mem := hγ
  spatial_smooth r := by
    have hmap : ContMDiffOn (spacetimeModel n)
        ((spacetimeModel n).prod (𝓡 n)) ∞
        (fun p : G.Point => (p, y r)) e.baseSet :=
      contMDiffOn_id.prodMk contMDiffOn_const
    exact (e.contMDiffOn_symm.comp hmap
      (fun _ hp => e.mem_target.mpr hp)).congr
        (fun p hp => e.mk_symm hp (y r))
  joint_smooth := by
    refine ⟨U ×ˢ e.baseSet, hU.prod e.open_baseSet,
      fun s hs => ⟨hJU hs, hγ s hs⟩, ?_⟩
    have hmap : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
        ((spacetimeModel n).prod (𝓡 n)) ∞
        (fun z : ℝ × G.Point => (z.2, y z.1)) (U ×ˢ e.baseSet) :=
      contMDiffOn_snd.prodMk (hy.contMDiffOn.comp contMDiffOn_fst (fun _ hz => hz.1))
    exact (e.contMDiffOn_symm.comp hmap
      (fun _ hz => e.mem_target.mpr hz.2)).congr
        (fun z hz => e.mk_symm hz.2 (y z.1))
  agrees := hY
  parameter_derivative s hs := by
    let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    have hd := (hy.contDiffAt (hU.mem_nhds (hJU hs))).differentiableAt (by simp)
    refine ⟨e.symmL ℝ (γ s) (deriv y s), ?_⟩
    simpa only [Function.comp_def, e.symmL_apply (hγ s hs)] using
      ((e.symmL ℝ (γ s)).hasFDerivAt.comp_hasDerivAt s hd.hasDerivAt)

theorem exists_pullbackExtensionInChart_Icc
    (e : Bundle.Trivialization (EuclideanSpace ℝ (Fin n))
      (Bundle.TotalSpace.proj : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
        G.Horizontal → G.Point)) [MemTrivializationAtlas e]
    {a b : ℝ} (hab : a < b)
    (hγ : ∀ s ∈ Set.Icc a b, γ s ∈ e.baseSet)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.spacetime.Horizontal) (γ s) (Y s)) (Set.Icc a b)) :
    Nonempty (M14PullbackExtension G γ (Set.Icc a b) Y) := by
  let y := fun s => (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
    (E := G.spacetime.Horizontal) (γ s) (Y s))).2
  have hpair := e.contMDiffOn.comp hY (fun s hs => e.mem_source.mpr (hγ s hs))
  have hy : ContDiffOn ℝ ∞ y (Set.Icc a b) :=
    ContMDiffOn.contDiffOn (fun s hs => (hpair s hs).snd)
  obtain ⟨z, hz, hzy⟩ := M08.exists_smooth_extension_Icc hab y hy
  refine ⟨pullbackExtensionInChart e isOpen_univ (Set.subset_univ _) z
    hz.contDiffOn hγ ?_⟩
  intro s hs
  rw [hzy hs]
  exact e.symm_apply_apply_mk (hγ s hs) (Y s)

end PoincareConjecture.M14
