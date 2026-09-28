import PoincareConjecture.Proofs.M25.Topology3D.Space3.ManifoldLocalInverse
import Mathlib.Topology.DiscreteSubset











set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
variable [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]



theorem exists_injective_neighborhood_of_mfderiv
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (x : M)
    (hdf : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  obtain ⟨e, hxe, he, _⟩ := exists_smooth_manifold_local_inverse f hf x hdf
  exact ⟨e.source, e.open_source, hxe, he ▸ e.injOn⟩



theorem finite_regular_fiber [CompactSpace M] [T2Space N]
    (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f) (y : N)
    (hregular : ∀ x, f x = y →
      Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x)) :
    (f ⁻¹' {y}).Finite := by
  have hcompact : IsCompact (f ⁻¹' {y}) :=
    (isClosed_singleton.preimage hf.continuous).isCompact
  apply hcompact.finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  have hxy : f x = y := hx
  obtain ⟨U, hU, hxU, hinj⟩ :=
    exists_injective_neighborhood_of_mfderiv f hf x (hregular x hxy)
  refine ⟨U, hU, ?_⟩
  ext z
  constructor
  · rintro ⟨hzU, hzy⟩
    exact mem_singleton_iff.mpr (hinj hzU hxU ((show f z = y from hzy).trans hxy.symm))
  · intro hzx
    have hz : z = x := hzx
    subst z
    exact ⟨hxU, hx⟩

end PoincareConjecture.M25.Topology3D
