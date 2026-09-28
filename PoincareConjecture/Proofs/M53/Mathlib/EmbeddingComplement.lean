import PoincareConjecture.Proofs.M53.Mathlib.EmbeddedLocalSlice
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E' N]
  {n : ℕ∞ω} {f : M → N} {x : M}

theorem IsImmersionAtOfComplement.not_mem_interior_range [Nontrivial F]
    (h : IsImmersionAtOfComplement F 𝓘(𝕜, E) 𝓘(𝕜, E') n f x)
    (hf : IsEmbedding f) : f x ∉ interior (range f) := by
  let : PerfectSpace F := perfectSpace_of_module 𝕜 F
  intro hx
  obtain ⟨V, hV, hxV, hVs, hslice⟩ := h.exists_isOpen_range_iff hf
  let U := V ∩ interior (range f)
  have hU : IsOpen U := hV.inter isOpen_interior
  have hUs : U ⊆ h.codChart.source := fun _ hy => hVs hy.1
  have hopen : IsOpen (Prod.snd '' (h.equiv.symm '' (h.codChart '' U))) :=
    isOpenMap_snd _ (h.equiv.symm.toHomeomorph.isOpenMap _
      (h.codChart.isOpen_image_of_subset_source hU hUs))
  have hsingle : Prod.snd '' (h.equiv.symm '' (h.codChart '' U)) = ({0} : Set F) := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨h.equiv.symm (h.codChart (f x)),
        ⟨h.codChart (f x), ⟨f x, ⟨hxV, hx⟩, rfl⟩, rfl⟩,
        (hslice (f x) hxV).mp (mem_range_self x)⟩
    · rintro z ⟨p, ⟨q, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
      exact (hslice y hy.1).mp (interior_subset hy.2)
  rw [hsingle] at hopen
  exact not_isOpen_singleton (0 : F) hopen

theorem IsSmoothEmbedding.interior_range_eq_empty
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (hf : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n f)
    (hdim : Module.finrank 𝕜 E < Module.finrank 𝕜 E') :
    interior (range f) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨x, rfl⟩ := interior_subset hy
  obtain ⟨F, instF, inst𝕜F, h⟩ := hf.isImmersion.isImmersionAt x
  let := instF
  let := inst𝕜F
  let : FiniteDimensional 𝕜 (E × F) :=
    h.equiv.symm.toLinearEquiv.finiteDimensional
  let : FiniteDimensional 𝕜 F :=
    FiniteDimensional.of_injective (LinearMap.inr 𝕜 E F) (by
      intro a b hab
      exact congrArg Prod.snd hab)
  have hsum := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hsum
  have : Nontrivial F := (Module.finrank_pos_iff (R := 𝕜)).mp (by omega)
  exact h.not_mem_interior_range hf.isEmbedding hy

theorem IsSmoothEmbedding.dense_compl_range
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E']
    (hf : IsSmoothEmbedding 𝓘(𝕜, E) 𝓘(𝕜, E') n f)
    (hdim : Module.finrank 𝕜 E < Module.finrank 𝕜 E') :
    Dense (range f)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (hf.interior_range_eq_empty hdim)

end Manifold
