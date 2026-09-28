import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

open Set

variable {E K F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace F]

theorem IsZLattice.isCompact_range_of_periodic_prod (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : K × E → F) (hf : Continuous f)
    (hperiodic : ∀ k x z, z ∈ L → f (k, x + z) = f (k, x)) :
    IsCompact (range f) := by
  let g : C(E, C(K, F)) :=
    (⟨fun p : E × K => f (p.2, p.1), hf.comp continuous_swap⟩ : C(E × K, F)).curry
  have hg : IsCompact (range g) :=
    IsZLattice.isCompact_range_of_periodic L g g.continuous fun x z hz => by
      ext k
      exact hperiodic k x z hz
  have hcompact := (hg.prod (isCompact_univ : IsCompact (univ : Set K))).image
    (continuous_eval : Continuous (fun p : C(K, F) × K => p.1 p.2))
  have himage : (fun p : C(K, F) × K => p.1 p.2) '' (range g ×ˢ univ) = range f := by
    ext y
    constructor
    · rintro ⟨⟨a, k⟩, ⟨⟨x, rfl⟩, _⟩, rfl⟩
      exact ⟨(k, x), rfl⟩
    · rintro ⟨⟨k, x⟩, rfl⟩
      exact ⟨(g x, k), ⟨⟨x, rfl⟩, mem_univ k⟩, rfl⟩
  rwa [himage] at hcompact

theorem IsZLattice.exists_pos_displacement_bound_prod (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : K × E → E) (hf : Continuous f)
    (hequiv : ∀ k x z, z ∈ L → f (k, x + z) = f (k, x) + z) :
    ∃ C > 0, ∀ k x, ‖f (k, x) - x‖ ≤ C := by
  have hc : IsCompact (range (fun p : K × E => f p - p.2)) :=
    IsZLattice.isCompact_range_of_periodic_prod L _ (hf.sub continuous_snd) fun k x z hz => by
      rw [hequiv k x z hz, add_sub_add_right_eq_sub]
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun k x => hbound _ ⟨(k, x), rfl⟩⟩

theorem Homeomorph.exists_pos_displacement_bound_of_lattice (e : E ≃ₜ E)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hequiv : ∀ x z, z ∈ L → e (x + z) = e x + z) :
    ∃ C > 0, ∀ x, ‖e x - x‖ ≤ C := by
  have hc : IsCompact (range (fun x => e x - x)) :=
    IsZLattice.isCompact_range_of_periodic L _ (e.continuous.sub continuous_id) fun x z hz => by
      rw [hequiv x z hz, add_sub_add_right_eq_sub]
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun x => hbound _ ⟨x, rfl⟩⟩
