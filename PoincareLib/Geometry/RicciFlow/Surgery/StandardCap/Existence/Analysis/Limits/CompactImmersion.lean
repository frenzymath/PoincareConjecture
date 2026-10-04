import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.ManifoldOpenMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen

/-!
# Compact manifolds do not immerse in Euclidean space of the same dimension

An injective differential in equal finite dimension is bijective. The
inverse function theorem makes the image open. A nonempty compact image
would also be closed, hence all of the connected noncompact target.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; the compact-alternative
exclusion in the M34 unit-lifetime derivation, section 4.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- A smooth immersion into an equal-dimensional nonzero real normed
space rules out compactness of its nonempty domain (Theorem 12.28). -/
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

end PoincareMT.M34
