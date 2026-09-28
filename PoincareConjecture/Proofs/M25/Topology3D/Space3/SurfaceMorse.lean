import PoincareConjecture.Proofs.M25.Topology3D.Space3.MorseChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.GenericHeight

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem exists_surface_morse_chart (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hzero : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0)
    (hinj : Function.Injective (fderiv ℝ (fderiv ℝ
      (f ∘ (chartAt E x).symm)) (chartAt E x x))) :
    ∃ (σ τ : ℝ) (e : OpenPartialHomeomorph M (ℝ × ℝ)),
      σ * σ = 1 ∧ τ * τ = 1 ∧ x ∈ e.source ∧ e x = 0 ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      ∀ y ∈ e.source, f y = f x + σ * (e y).1 ^ 2 + τ * (e y).2 ^ 2 := by
  let c := chartAt E x
  let F : E → ℝ := f ∘ c.symm
  have hxc : x ∈ c.source := mem_chart_source E x
  have hcx : c x ∈ c.target := c.map_source hxc
  have hcs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hcc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c c.source :=
    contMDiffOn_chart
  have hF : ContDiffOn ℝ ∞ F c.target := (hf.comp_contMDiffOn hcs).contDiffOn
  have hd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) F (c x)
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (c.symm (c x))).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) :=
    (hf.mdifferentiable (by simp) (c.symm (c x))).hasMFDerivAt.comp (c x)
      ((hcs.contMDiffAt (c.open_target.mem_nhds hcx)).mdifferentiableAt
        (by simp)).hasMFDerivAt
  have hFzero : fderiv ℝ F (c x) = 0 := by
    rw [← mfderiv_eq_fderiv, hd.mfderiv]
    have hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (c.symm (c x)) = 0 := by
      rw [c.left_inv hxc]
      exact hzero
    rw [hz, ContinuousLinearMap.zero_comp]
    rfl
  obtain ⟨σ, τ, e0, hσ, hτ, hx0, _, he0, hes, hei, hform⟩ :=
    exists_morse_chart hdim F c.open_target hF (c x) hcx hFzero hinj
  let e := c.trans e0
  refine ⟨σ, τ, e, hσ, hτ, ⟨hxc, hx0⟩, he0, ?_, ?_, ?_⟩
  · exact hes.contMDiffOn.comp (hcc.mono inter_subset_left) (fun _ hy => hy.2)
  · exact hcs.comp (hei.contMDiffOn.mono inter_subset_left) (fun _ hy => hy.2)
  · intro y hy
    have h := hform (c y) hy.2
    change f (c.symm (c y)) = f (c.symm (c x)) +
      σ * (e0 (c y)).1 ^ 2 + τ * (e0 (c y)).2 ^ 2 at h
    rw [c.left_inv hy.1, c.left_inv hxc] at h
    exact h

theorem exists_generic_collar_morse_height (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) :
    ∃ u : UnitTwoSphere,
      {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0}.Finite ∧
      InjOn (fun q : UnitTwoSphere => ⟪(u : E3), ψ (q, 0)⟫_ℝ)
        {q : UnitTwoSphere | mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0} ∧
      ∀ q : UnitTwoSphere,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q = 0 →
        ∃ (σ τ : ℝ) (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ)),
          σ * σ = 1 ∧ τ * τ = 1 ∧ q ∈ e.source ∧ e q = 0 ∧
          ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source ∧
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target ∧
          ∀ p ∈ e.source, ⟪(u : E3), ψ (p, 0)⟫_ℝ =
            ⟪(u : E3), ψ (q, 0)⟫_ℝ + σ * (e p).1 ^ 2 + τ * (e p).2 ^ 2 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨u, hfinite, hdistinct, hhessian⟩ := exists_generic_collar_height ψ hψ
  refine ⟨u, hfinite, hdistinct, ?_⟩
  intro q hq
  apply exists_surface_morse_chart (E := E2) (by simp [E2])
    (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) _ q hq (hhessian q hq)
  exact (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
    (collar_central_contMDiff ψ hψ)

end PoincareConjecture.M25.Topology3D
