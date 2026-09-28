import PoincareConjecture.Definitions.M14PathCalculus









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem horizontal_parameter_hasDerivAt_of_contMDiffAt
    (V : ℝ → HorizontalSection G.spacetime)
    (s : ℝ) (p : G.Point)
    (hV : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.spacetime.Horizontal) z.2 (V z.1 z.2))
        (s, p)) : ∃ d : G.Horizontal p,
      HasDerivAt (fun r => V r p) d s := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal p
  have hp : p ∈ e.baseSet :=
    mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal p
  have hf := hV.comp s (contMDiffAt_id.prodMk (contMDiffAt_const (c := p)))
  have hc := ((e.contMDiffOn.contMDiffAt
    (e.open_source.mem_nhds (e.mem_source.mpr hp))).comp s hf).snd
  let y : ℝ → EuclideanSpace ℝ (Fin n) := fun r =>
    (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := G.spacetime.Horizontal) p (V r p))).2
  have hy : ContDiffAt ℝ ∞ y s := hc.contDiffAt
  have heq : (fun r => V r p) = (e.symmL ℝ p) ∘ y := by
    funext r
    simp only [Function.comp_apply, e.symmL_apply hp, y]
    exact (e.symm_apply_apply_mk hp (V r p)).symm
  rw [heq]
  exact ⟨_, (e.symmL ℝ p).hasFDerivAt.comp_hasDerivAt s
    (hy.differentiableAt (by simp)).hasDerivAt⟩



theorem horizontal_parameter_hasDerivAt
    (V : ℝ → HorizontalSection G.spacetime)
    (hV : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.spacetime.Horizontal) z.2 (V z.1 z.2)))
    (s : ℝ) (p : G.Point) : ∃ d : G.Horizontal p,
      HasDerivAt (fun r => V r p) d s :=
  horizontal_parameter_hasDerivAt_of_contMDiffAt V s p (hV (s, p))




noncomputable def pullbackExtensionOfGlobalSmooth
    {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}
    (V : ℝ → HorizontalSection G.spacetime)
    (hV : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.spacetime.Horizontal) z.2 (V z.1 z.2)))
    (hY : ∀ s ∈ J, V s (γ s) = Y s) : M14PullbackExtension G γ J Y where
  extension := V
  domain := Set.univ
  domain_open := isOpen_univ
  graph_mem := fun _ _ => Set.mem_univ _
  spatial_smooth r :=
    (hV.comp ((contMDiff_const (c := r)).prodMk contMDiff_id)).contMDiffOn
  joint_smooth := ⟨Set.univ, isOpen_univ, fun _ _ => Set.mem_univ _, hV.contMDiffOn⟩
  agrees := hY
  parameter_derivative s _ := horizontal_parameter_hasDerivAt V hV s (γ s)

end PoincareConjecture.M14
