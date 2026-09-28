import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]

theorem exists_smooth_manifold_local_inverse
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (x : M)
    (hdf : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    ∃ e : OpenPartialHomeomorph M N, x ∈ e.source ∧ (e : M → N) = f ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) (f x)) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let c := chartAt E (f x)
  let U := f ⁻¹' c.source
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hcx : f x ∈ c.source := mem_chart_source E (f x)
  have hcs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c c.source := contMDiffOn_chart
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (c ∘ f) U :=
    hcs.comp hf.contMDiffOn (fun _ hx => hx)
  have hc := mdifferentiable_chart (I := 𝓘(ℝ, E)) (f x)
  have hb : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c ∘ f) x) := by
    rw [mfderiv_comp x (hc.mdifferentiableAt hcx) (hf.mdifferentiable (by simp) x)]
    exact (hc.mfderiv_bijective hcx).comp
      ⟨hdf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) x) =
          Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) (f x)) from rfl)).mp hdf⟩
  obtain ⟨e0, hx0, h0U, h0, h0i⟩ :=
    exists_manifold_source_local_inverse (c ∘ f) hU hg x hcx hb
  let e := e0.trans c.symm
  have hxe : x ∈ e.source := by
    refine ⟨hx0, ?_⟩
    change e0 x ∈ c.target
    rw [h0 hx0]
    exact c.map_source hcx
  have hef : EqOn e f e.source := by
    intro y hy
    change c.symm (e0 y) = f y
    rw [h0 hy.1]
    exact c.left_inv (h0U hy.1)
  have hei : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
    h0i.comp (hcs.mono inter_subset_left) (fun _ hy => hy.2)
  let J : OpenPartialHomeomorph M N := {
    toFun := f
    invFun := e.symm
    source := e.source
    target := e.target
    map_source' := fun y hy => hef hy ▸ e.map_source hy
    map_target' := fun _ hy => e.map_target hy
    left_inv' := fun y hy => by rw [← hef hy]; exact e.left_inv hy
    right_inv' := fun y hy => (hef (e.map_target hy)).symm.trans (e.right_inv hy)
    open_source := e.open_source
    open_target := e.open_target
    continuousOn_toFun := hf.continuous.continuousOn
    continuousOn_invFun := e.continuousOn_symm }
  exact ⟨J, hxe, rfl, hei⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ N] in

theorem mfderiv_injective_of_local_right_inverse
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (g : N → M) (x : N)
    (hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) g x)
    (hfg : f ∘ g =ᶠ[𝓝 x] id) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (g x)) := by
  have hd := (hf.mdifferentiable (by simp) (g x)).hasMFDerivAt.comp x hg.hasMFDerivAt
  have hmap := hd.mfderiv
  rw [hfg.mfderiv_eq, mfderiv_id] at hmap
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (g x)
  let B : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x
  have hAB : ContinuousLinearMap.id ℝ E = A.comp B := hmap
  have hA : Function.Surjective A := by
    intro y
    exact ⟨B y, (congrArg (fun L : E →L[ℝ] E => L y) hAB).symm⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show Module.finrank ℝ E = Module.finrank ℝ E from rfl)).mpr hA

end PoincareConjecture.M25.Topology3D
