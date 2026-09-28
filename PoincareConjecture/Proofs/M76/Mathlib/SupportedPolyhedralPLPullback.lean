import PoincareConjecture.Proofs.M76.Mathlib.FinitePLNeighborhoodExtension
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Indicator

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E G F ι : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_compactly_supported_PL_pullback
    (e : ι → OpenPartialHomeomorph M E)
    {g : M → G} (hg : Continuous g)
    (hgPL : ∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target)
    (K : SimplicialComplex ℝ G) {C : Set M} (hC : IsCompact C)
    (hgK : MapsTo g C K.space)
    {f : G → F} (hf : FinitePiecewiseAffineOn f K.space)
    {P : Set G} (hP : IsClosed P)
    (hfzero : ∀ y ∈ K.space, y ∉ P → f y = 0)
    (hinside : ∀ x ∈ C, g x ∈ P → x ∈ interior C) :
    ∃ (z : M → F) (Q : Set M), IsCompact Q ∧ Q ⊆ interior C ∧
      Continuous z ∧ EqOn z (f ∘ g) C ∧ (∀ x, x ∉ Q → z x = 0) ∧
      ∀ i, LocallyPiecewiseAffineOn (z ∘ (e i).symm) (e i).target := by
  classical
  let Q : Set M := C ∩ g ⁻¹' P
  have hQ : IsCompact Q := hC.inter_right (hP.preimage hg)
  have hQC : Q ⊆ interior C := fun x hx => hinside x hx.1 hx.2
  let z : M → F := C.indicator (f ∘ g)
  have hzon (x : M) (hx : x ∈ C) : z x = f (g x) := indicator_of_mem hx _
  have hzoff (x : M) (hx : x ∉ Q) : z x = 0 := by
    by_cases hxC : x ∈ C
    · rw [hzon x hxC]
      exact hfzero (g x) (hgK hxC) (fun hxP => hx ⟨hxC, hxP⟩)
    · exact indicator_of_notMem hxC _
  have hz : Continuous z := by
    apply continuous_indicator
    · intro x hx
      have hxC : x ∈ C := hC.isClosed.closure_subset hx.1
      exact hfzero (g x) (hgK hxC) (fun hxP => hx.2 (hinside x hxC hxP))
    · rw [hC.isClosed.closure_eq]
      exact hf.continuousOn.comp hg.continuousOn hgK
  obtain ⟨a, V, hV, hKV, ha, haf⟩ := hf.exists_locallyPiecewiseAffine_extension
  refine ⟨z, Q, hQ, hQC, hz, fun x hx => hzon x hx, hzoff, ?_⟩
  intro i
  let U : Set E := (e i).target ∩ (e i).symm ⁻¹' interior C
  have hU : IsOpen U := (e i).symm.continuousOn.isOpen_inter_preimage
    (e i).open_target isOpen_interior
  have hUin : U ⊆ (e i).target ∩ (g ∘ (e i).symm) ⁻¹' V :=
    fun y hy => ⟨hy.1, hKV (hgK (interior_subset hy.2))⟩
  have hzU : LocallyPiecewiseAffineOn (z ∘ (e i).symm) U := by
    apply ((ha.comp (hgPL i)).mono hU hUin).congr
    intro y hy
    change a (g ((e i).symm y)) = z ((e i).symm y)
    rw [hzon _ (interior_subset hy.2)]
    exact haf (hgK (interior_subset hy.2))
  let W : Set E := (e i).target ∩ (e i).symm ⁻¹' Qᶜ
  have hW : IsOpen W := (e i).symm.continuousOn.isOpen_inter_preimage
    (e i).open_target hQ.isClosed.isOpen_compl
  have hzW : LocallyPiecewiseAffineOn (z ∘ (e i).symm) W := by
    apply (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ E (0 : F)) hW).congr
    intro y hy
    exact (hzoff ((e i).symm y) hy.2).symm
  apply LocallyPiecewiseAffineOn.locality
  intro y hy
  by_cases hyC : (e i).symm y ∈ interior C
  · exact ⟨U, ⟨hy, hyC⟩, hzU.mono ((e i).open_target.inter hU) inter_subset_right⟩
  · exact ⟨W, ⟨hy, fun hyQ => hyC (hQC hyQ)⟩,
      hzW.mono ((e i).open_target.inter hW) inter_subset_right⟩

end OpenPartialHomeomorph
