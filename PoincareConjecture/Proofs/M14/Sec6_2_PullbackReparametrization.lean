import PoincareConjecture.Proofs.M14.Sec6_2_ProductExtension
import PoincareConjecture.Proofs.M14.Mathlib.PullbackSectionSmooth
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackMetric









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J K : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}




noncomputable def pullbackExtensionSmulComp (E : M14PullbackExtension G γ J Y)
    (f c : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hc : ContDiff ℝ ∞ c) (hmap : MapsTo f K J) :
    M14PullbackExtension G (γ ∘ f) K (fun s => c s • Y (f s)) := by
  let W : ℝ → HorizontalSection G.spacetime := fun s q => c s • E.extension (f s) q
  let U := E.joint_smooth.choose
  have hU := E.joint_smooth.choose_spec.1
  have hgraph := E.joint_smooth.choose_spec.2.1
  have hE := E.joint_smooth.choose_spec.2.2
  let k := fun z : ℝ × G.Point => (f z.1, z.2)
  let N := k ⁻¹' U
  have hk : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) ∞ k :=
    (hf.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have hN : IsOpen N := hU.preimage hk.continuous
  have hfield := hE.comp hk.contMDiffOn (fun _ hz => hz)
  let base : ContMDiffMap ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n) (ℝ × G.Point) G.Point ∞ := ⟨Prod.snd, contMDiff_snd⟩
  let : ∀ z, AddCommGroup (((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (AddCommGroup (G.Horizontal (base z)))
  let : ∀ z, Module ℝ (((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (Module ℝ (G.Horizontal (base z)))
  let V : ∀ z, ((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z :=
    fun z => E.extension (f z.1) z.2
  have hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z (V z)) N := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base V N z).mpr (hfield z hz)
  have hscalar : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × G.Point => c z.1) := hc.contMDiff.comp contMDiff_fst
  have hscaled := hscalar.contMDiffOn.smul_section hV
  have hW : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) z.2 (W z.1 z.2)) N := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base
      (fun z => c z.1 • V z) N z).mp (hscaled z hz)
  refine {
    extension := W
    domain := E.domain
    domain_open := E.domain_open
    graph_mem := fun s hs => E.graph_mem (f s) (hmap hs)
    spatial_smooth := ?_
    joint_smooth := ⟨N, hN, fun s hs => hgraph (f s) (hmap hs), hW⟩
    agrees := ?_
    parameter_derivative := ?_ }
  · intro s
    exact (E.spatial_smooth (f s)).const_smul_section
  · intro s hs
    exact congrArg (fun v : G.Horizontal (γ (f s)) => c s • v) (E.agrees (f s) (hmap hs))
  · intro s hs
    exact horizontal_parameter_hasDerivAt_of_contMDiffAt W s (γ (f s))
      ((hW _ (hgraph (f s) (hmap hs))).contMDiffAt (hN.mem_nhds (hgraph (f s) (hmap hs))))




theorem horizontalCovariantDerivative_smul_comp
    (E : M14PullbackExtension G γ J Y) (f c : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : ContDiff ℝ ∞ c) (hmap : MapsTo f K J)
    {s : ℝ} (hs : s ∈ K) (hK : K ∈ 𝓝 s) (hJ : J ∈ 𝓝 (f s))
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ (f s)) :
    M14HorizontalCovariantDerivative G (γ ∘ f) K (fun r => c r • Y (f r))
        (pullbackExtensionSmulComp E f c hf hc hmap) s =
      deriv c s • Y (f s) + (c s * deriv f s) •
        M14HorizontalCovariantDerivative G γ J Y E (f s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (γ (f s))) :=
    (metric.toCore (γ (f s))).toNormedAddCommGroupOfTopology
      (metric.continuousAt (γ (f s))) (metric.isVonNBounded (γ (f s)))
  let : InnerProductSpace ℝ (G.Horizontal (γ (f s))) :=
    .ofCoreOfTopology (metric.toCore (γ (f s)))
      (metric.continuousAt (γ (f s))) (metric.isVonNBounded (γ (f s)))
  have hf' := (hf.differentiable (by simp) s).hasDerivAt
  have hc' := (hc.differentiable (by simp) s).hasDerivAt
  obtain ⟨d, hd⟩ := E.parameter_derivative (f s) (hmap hs)
  have ht := (hc'.smul (hd.differentiableAt.hasDerivAt.scomp s hf')).deriv
  have hparam : deriv (fun r => c r • E.extension (f r) (γ (f s))) s =
      c s • (deriv f s • deriv (fun r => E.extension r (γ (f s))) (f s)) +
        deriv c s • Y (f s) := by
    simpa only [Pi.smul_def', Function.comp_def, E.agrees (f s) (hmap hs)] using ht
  have hspace := ((E.spatial_smooth (f s) (γ (f s))
    (E.graph_mem (f s) (hmap hs))).contMDiffAt
      (E.domain_open.mem_nhds (E.graph_mem (f s) (hmap hs)))).mdifferentiableAt (by simp)
  have hcov := (rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise).smul_const
    (c s) hspace
  have hfderiv : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) f s (1 : ℝ) =
      deriv f s • (1 : TangentSpace (𝓘(ℝ, ℝ)) (f s)) := by
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ)) (f s) => L 1) hf'.hasFDerivAt.hasMFDerivAt.mfderiv
    change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) f s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv f s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
      mul_one, one_mul] using hv
  have hchain := mfderiv_comp_apply s hγ hf'.differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hfderiv, map_smul] at hchain
  change deriv (fun r => c r • E.extension (f r) (γ (f s))) s +
      rawHorizontalCovariantDerivative G.leafwise (c s • E.extension (f s)) (γ (f s))
        (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (γ ∘ f) K s (1 : ℝ)) = _
  rw [mfderivWithin_of_mem_nhds hK, hchain, hcov]
  rw [hparam]
  simp only [M14HorizontalCovariantDerivative, mfderivWithin_of_mem_nhds hJ,
    smul_apply, map_smul, smul_smul, smul_add, mul_comm (deriv f s) (c s)]
  abel

end PoincareConjecture.M14
