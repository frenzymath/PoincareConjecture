import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationZeroChart













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff

namespace PoincareConjecture.M65Perturbation

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X]

set_option maxHeartbeats 600000 in





theorem finite_fibers_of_zero_charts (mu : Measure E) [IsAddHaarMeasure mu]
    (K : Set X) (hK : IsCompact K) (parameter : X → E)
    (hparameter : ContinuousOn parameter K)
    (U : ι → Set E) (W : ι → Set X) (projection : ι → E → E)
    (coordinate : ι → X → E) (reconstruct : ι → E → X)
    (hU : ∀ i, IsOpen (U i)) (hW : ∀ i, IsOpen (W i))
    (hprojection : ∀ i, ContDiffOn ℝ 1 (projection i) (U i))
    (hcoordinate : ∀ i, ContinuousOn (coordinate i) (W i))
    (hcover : K ⊆ ⋃ i, W i)
    (hchart : ∀ i x, x ∈ K → x ∈ W i →
      coordinate i x ∈ U i ∧ projection i (coordinate i x) = parameter x ∧
        reconstruct i (coordinate i x) = x) :
    ∃ Bad : Set E, mu Bad = 0 ∧ ∀ p ∉ Bad, {x ∈ K | parameter x = p}.Finite := by
  classical
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover W hW hcover
  let Bad := ⋃ i ∈ I, projection i '' {v ∈ U i | (fderiv ℝ (projection i) v).det = 0}
  have hBad : mu Bad = 0 := by
    apply (measure_biUnion_null_iff I.countable_toSet).mpr
    intro i _
    exact (critical_image_null_and_fibers_discrete mu (projection i) (U i) (hU i)
      (hprojection i)).1
  refine ⟨Bad, hBad, ?_⟩
  intro p hp
  have hclosed : IsClosed {x ∈ K | parameter x = p} :=
    hK.isClosed.isClosed_eq hparameter continuousOn_const
  apply (hK.of_isClosed_subset hclosed (fun _ hx => hx.1)).finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hI hx.1)
  obtain ⟨hxu, hxp, hxr⟩ := hchart i x hx.1 hxi
  have hdet : (fderiv ℝ (projection i) (coordinate i x)).det ≠ 0 := by
    intro hzero
    apply hp
    exact mem_iUnion₂.mpr ⟨i, hi, coordinate i x, ⟨hxu, hzero⟩, hxp.trans hx.2⟩
  obtain ⟨e, hxe, he⟩ := exists_local_inverse_of_det_ne_zero (projection i) (coordinate i x)
    ((hprojection i).contDiffAt ((hU i).mem_nhds hxu)) hdet
  let V := W i ∩ coordinate i ⁻¹' e.source
  have hV : IsOpen V := (hcoordinate i).isOpen_inter_preimage (hW i) e.open_source
  refine ⟨V, hV, subset_antisymm ?_ (singleton_subset_iff.mpr ⟨⟨hxi, hxe⟩, hx⟩)⟩
  intro y hy
  obtain ⟨_hyu, hyp, hyr⟩ := hchart i y hy.2.1 hy.1.1
  have heq : coordinate i y = coordinate i x := by
    apply e.injOn hy.1.2 hxe
    rw [he]
    exact (hyp.trans hy.2.2).trans (hxp.trans hx.2).symm
  exact mem_singleton_iff.mpr (hyr.symm.trans ((congrArg (reconstruct i) heq).trans hxr))

end PoincareConjecture.M65Perturbation
