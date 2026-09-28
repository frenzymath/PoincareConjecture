import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarParameter











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable [Nonempty M]



theorem exists_smooth_product_chart (ψ : M × ℝ → F) {U : Set (M × ℝ)} (hU : IsOpen U)
    (hψ : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ ψ U)
    (hi : InjOn ψ U)
    (hd : ∀ p ∈ U, Function.Injective
      (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ψ p))
    (hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F) :
    ∃ e : OpenPartialHomeomorph (M × ℝ) F, (e : M × ℝ → F) = ψ ∧
      e.source = U ∧ e.target = ψ '' U ∧
      ContMDiffOn 𝓘(ℝ, F) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
  let : ChartedSpace (E × ℝ) (M × ℝ) := prodChartedSpace E M ℝ ℝ
  let : IsManifold 𝓘(ℝ, E × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod M ℝ
  have hf : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ∞ ψ U := by
    rwa [modelWithCornersSelf_prod]
  have hb (p : M × ℝ) (hp : p ∈ U) :
      Function.Bijective (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ψ p) := by
    have hinj : Function.Injective (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ψ p) := by
      change Function.Injective
        (fun v : E × ℝ => (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ψ p) v : E × ℝ → F)
      rw [modelWithCornersSelf_prod]
      exact hd p hp
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv 𝓘(ℝ, E × ℝ) 𝓘(ℝ, F) ψ p).toLinearMap) hdim).mp hinj⟩
  let e := manifoldOpenChart ψ hU hf hb hi
  refine ⟨e, rfl, rfl, rfl, ?_⟩
  have he := manifoldOpenChart_symm_contMDiffOn ψ hU hf hb hi
  rwa [modelWithCornersSelf_prod] at he




theorem exists_collar_defining_function (ψ : M × ℝ → F) {U : Set (M × ℝ)}
    (hU : IsOpen U)
    (hψ : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ ψ U)
    (hi : InjOn ψ U)
    (hd : ∀ p ∈ U, Function.Injective
      (mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ψ p))
    (hdim : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ F) :
    ∃ ρ : F → ℝ, ContDiffOn ℝ ∞ ρ (ψ '' U) ∧
      (∀ p ∈ U, ρ (ψ p) = p.2) ∧ ∀ y ∈ ψ '' U, fderiv ℝ ρ y ≠ 0 := by
  obtain ⟨e, he, hsource, htarget, hinv⟩ :=
    exists_smooth_product_chart ψ hU hψ hi hd hdim
  have hforward :
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ e e.source := by
    rw [hsource, he]
    exact hψ
  refine ⟨collarParameter e, ?_, ?_, ?_⟩
  · rw [← htarget]
    exact collarParameter_contDiffOn e hinv
  · intro p hp
    rw [← he]
    exact collarParameter_apply e p (hsource.symm ▸ hp)
  · rintro y ⟨p, hp, rfl⟩
    rw [← he]
    exact collarParameter_fderiv_ne_zero e hinv hforward p (hsource.symm ▸ hp)

end PoincareConjecture.M25.Topology3D
