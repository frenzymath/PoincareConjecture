import PoincareConjecture.Proofs.M34.Mathlib.ManifoldOpenMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34



theorem not_isCompact_univ_of_euclidean_immersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [hfinite : FiniteDimensional ℝ E] [Nontrivial E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (x0 : M) (f : M → E) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    ¬ IsCompact (univ : Set M) := by
  intro hcompact
  have hbij (x : M) : Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) := by
    let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) x) := by
      unfold TangentSpace
      exact hfinite
    let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E) (f x)) := by
      unfold TangentSpace
      exact hfinite
    have hd : Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) x) =
        Module.finrank ℝ (TangentSpace 𝓘(ℝ, E) (f x)) := rfl
    exact ⟨hinj x, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp (hinj x)⟩
  have hclosed := hcompact.image hf.continuous
  have hopen : IsOpen (f '' univ) :=
    isOpen_image_of_contMDiffOn_mfderiv_bijective isOpen_univ hf.contMDiffOn
      (fun x _ => hbij x)
  have hall : f '' univ = univ :=
    (show IsClopen (f '' univ) from ⟨hclosed.isClosed, hopen⟩).eq_univ
      ⟨f x0, x0, mem_univ _, rfl⟩
  exact noncompact_univ E (hall ▸ hclosed)

end PoincareConjecture.M34
