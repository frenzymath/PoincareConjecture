import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_complementary_scalar_form (hdim : Module.finrank ℝ E = 2)
    (D : E →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ l : E →L[ℝ] ℝ, Function.Bijective (l.prod D) := by
  have hDlin : D.toLinearMap ≠ 0 := by
    intro h
    apply hD
    ext v
    exact congrArg (fun A : E →ₗ[ℝ] ℝ => A v) h
  have hker : Module.finrank ℝ D.ker = 1 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hDlin
    change Module.finrank ℝ D.ker + 1 = Module.finrank ℝ E at h
    omega
  obtain ⟨P, hP⟩ := D.ker_closedComplemented_of_finiteDimensional_range
  let k : D.ker ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (hker.trans (Module.finrank_self ℝ).symm)
  let l : E →L[ℝ] ℝ := k.toContinuousLinearMap.comp P
  have hinj : Function.Injective (l.prod D) := by
    intro x y hxy
    have hl : l x = l y := congrArg Prod.fst hxy
    have hd : D x = D y := congrArg Prod.snd hxy
    have hxyker : x - y ∈ D.ker := by
      change D (x - y) = 0
      rw [map_sub, hd, sub_self]
    have hp : P (x - y) = 0 := by
      apply k.injective
      change l (x - y) = k 0
      rw [map_sub, hl, sub_self, map_zero]
    have hz : x - y = 0 := congrArg Subtype.val ((hP ⟨x - y, hxyker⟩).symm.trans hp)
    exact sub_eq_zero.mp hz
  exact ⟨l, hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mp hinj⟩

theorem exists_regular_function_chart (hdim : Module.finrank ℝ E = 2)
    (f : E → ℝ) {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (x : E) (hx : x ∈ U) (hD : fderiv ℝ f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ), x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ y ∈ e.source, (e y).2 = f y := by
  obtain ⟨l, hl⟩ := exists_complementary_scalar_form hdim (fderiv ℝ f x) hD
  let g : E → ℝ × ℝ := fun y => (l y, f y)
  have hg : ContDiffOn ℝ ∞ g U := l.contDiff.contDiffOn.prodMk hf
  have hd : fderiv ℝ g x = l.prod (fderiv ℝ f x) :=
    (l.hasFDerivAt.prodMk
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv
  obtain ⟨e, hxe, heU, he, hei, _⟩ :=
    PoincareConjecture.Proofs.M09.exists_smooth_local_inverse g U hU hg x hx (by rw [hd]; exact hl)
  refine ⟨e, hxe, heU, ?_, hei, ?_⟩
  · rw [he]
    exact hg.mono heU
  · intro y _
    exact congrArg Prod.snd (congrFun he y)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_surface_regular_chart (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hD : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph M (ℝ × ℝ), x ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      ∀ y ∈ e.source, (e y).2 = f y := by
  let c := chartAt E x
  let F : E → ℝ := f ∘ c.symm
  have hxc : x ∈ c.source := mem_chart_source E x
  have hcx : c x ∈ c.target := c.map_source hxc
  have hcs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hcc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c c.source := contMDiffOn_chart
  have hF : ContDiffOn ℝ ∞ F c.target := (hf.comp_contMDiffOn hcs).contDiffOn
  have hc := (mdifferentiable_chart (I := 𝓘(ℝ, E)) x).symm
  have hd : fderiv ℝ F (c x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (c.symm (c x))).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x)) := by
    rw [← mfderiv_eq_fderiv]
    exact ((hf.mdifferentiable (by simp) (c.symm (c x))).hasMFDerivAt.comp (c x)
      (hc.mdifferentiableAt hcx).hasMFDerivAt).mfderiv
  have hFD : fderiv ℝ F (c x) ≠ 0 := by
    intro hz
    have h : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (c.symm (c x)) = 0 := by
      ext v
      obtain ⟨w, rfl⟩ := (hc.mfderiv_bijective hcx).surjective v
      exact congrArg (fun A : E →L[ℝ] ℝ => A w) (hd.symm.trans hz)
    apply hD
    rwa [c.left_inv hxc] at h
  obtain ⟨e0, hx0, _, hes, hei, hecoord⟩ :=
    exists_regular_function_chart hdim F c.open_target hF (c x) hcx hFD
  let e := c.trans e0
  refine ⟨e, ⟨hxc, hx0⟩, ?_, ?_, ?_⟩
  · exact hes.contMDiffOn.comp (hcc.mono inter_subset_left) (fun _ hy => hy.2)
  · exact hcs.comp (hei.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
  · intro y hy
    exact (hecoord (c y) hy.2).trans (congrArg f (c.left_inv hy.1))

end PoincareConjecture.M25.Topology3D
