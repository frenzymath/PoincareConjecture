import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Compactly supported extensions of local smooth fields

Smooth cutoff functions extend a field from a neighborhood of a compact
set, retaining every linear first integral. This is the localization
step for the height-preserving isotopies in Hatcher, Notes on Basic
3-Manifold Topology, Lemma 1.2, pp. 2-3.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold Topology

namespace PoincareMT.M25.Topology3D

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A compact set in an open set admits a smooth compactly supported
cutoff equal to one on a neighborhood; Hatcher's local moves, Lemma 1.2. -/
theorem exists_compact_smooth_cutoff [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, ρ x = 1) ∧ ∀ x, ρ x ∈ Icc 0 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨ρ, hnear, hzero, hrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKL (n := (⊤ : ℕ∞))
  have hs : Function.support ρ ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hzero x hxL)
  have hts : tsupport ρ ⊆ L := closure_minimal hs hL.isClosed
  exact ⟨ρ, ρ.contMDiff.contDiff, hL.of_isClosed_subset (isClosed_tsupport ρ) hts,
    hts.trans hLU, hnear, hrange⟩

/-- Multiplication by a cutoff whose closed support lies in the smooth
domain gives a globally smooth function, regardless of values outside. -/
theorem contDiff_cutoff_smul {U : Set E} (hU : IsOpen U)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hs : tsupport ρ ⊆ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => ρ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport ρ
  · exact hρ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hs hx)))
  · have heq : (fun y => ρ y • f y) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- A local smooth field extends with compact support while agreeing on
a neighborhood of the prescribed compact set; Hatcher, Lemma 1.2. -/
theorem exists_compactField_extension [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ U ∧ ∀ᶠ x in 𝓝ˢ K, g x = f x := by
  obtain ⟨ρ, hρ, hcompact, hs, hnear, _⟩ := exists_compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => ρ x • f x, contDiff_cutoff_smul hU ρ hρ hs f hf,
    hcompact.smul_right, (tsupport_smul_subset_left ρ f).trans hs, ?_⟩
  filter_upwards [hnear] with x hx
  rw [hx, one_smul]

omit [NormedSpace ℝ E] in
/-- A scalar cutoff preserves linear constraints on the field, including
the vanishing vertical component needed for height-preserving isotopies. -/
theorem cutoff_smul_preserves_linear {U : Set E} (ρ : E → ℝ)
    (hs : tsupport ρ ⊆ U) (f : E → F) (A : F →L[ℝ] G)
    (hA : ∀ x ∈ U, A (f x) = 0) (x : E) : A (ρ x • f x) = 0 := by
  by_cases hx : ρ x = 0
  · simp only [hx, zero_smul, map_zero]
  · rw [map_smul, hA x (hs (subset_tsupport ρ hx)), smul_zero]

/-- Compact localization preserves point-dependent linear constraints,
including annihilation of the defining-function differential. The
constraint family needs no regularity because it is checked pointwise. -/
theorem exists_compactField_extension_preserving [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U) (A : E → F →L[ℝ] G)
    (hA : ∀ x ∈ U, A x (f x) = 0) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, g x = f x) ∧ ∀ x, A x (g x) = 0 := by
  obtain ⟨ρ, hρ, hcompact, hs, hnear, _⟩ := exists_compact_smooth_cutoff hK hU hKU
  refine ⟨fun x => ρ x • f x, contDiff_cutoff_smul hU ρ hρ hs f hf,
    hcompact.smul_right, (tsupport_smul_subset_left ρ f).trans hs, ?_, ?_⟩
  · filter_upwards [hnear] with x hx
    rw [hx, one_smul]
  · intro x
    by_cases hx : ρ x = 0
    · simp only [hx, zero_smul, map_zero]
    · rw [map_smul, hA x (hs (subset_tsupport ρ hx)), smul_zero]

end PoincareMT.M25.Topology3D
