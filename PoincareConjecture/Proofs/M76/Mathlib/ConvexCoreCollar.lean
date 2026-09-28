import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.DenselyOrdered











set_option autoImplicit false

open Set Filter
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]




theorem IsCompact.exists_convex_innerCore {C U : Set E} (hC : IsCompact C)
    (hc : Convex ℝ C) (hi : (interior C).Nonempty) (hU : IsOpen U)
    (hfront : frontier C ⊆ U) :
    ∃ D : Set E, IsCompact D ∧ Convex ℝ D ∧ (interior D).Nonempty ∧
      D ⊆ interior C ∧ C \ interior D ⊆ U := by
  obtain ⟨p, hp⟩ := hi
  let K := C \ U
  have hK : IsCompact K := hC.diff hU
  have hKi : K ⊆ interior C := by
    intro x hx
    by_contra hxi
    exact hx.2 (hfront (by
      rw [frontier, hC.isClosed.closure_eq]
      exact ⟨hx.1, hxi⟩))
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, ∀ x ∈ K, t⁻¹ • (x - p) + p ∈ interior C := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hcont : ContinuousAt (fun z : ℝ × E => z.1⁻¹ • (z.2 - p) + p) (1, x) :=
      ((continuousAt_fst.inv₀ one_ne_zero).smul
        (continuousAt_snd.sub continuousAt_const)).add continuousAt_const
    apply hcont.eventually_mem
    simpa only [inv_one, one_smul, sub_add_cancel] using
      isOpen_interior.mem_nhds (hKi hx)
  have hparam : ∀ᶠ t : ℝ in 𝓝[<] 1,
      0 < t ∧ t < 1 ∧ ∀ x ∈ K, t⁻¹ • (x - p) + p ∈ interior C := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      (eventually_gt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hpos hlt
    exact ⟨hpos, hlt, ht⟩
  obtain ⟨t, ht0, ht1, htK⟩ := hparam.exists
  let D := AffineMap.homothety p t '' C
  have hopen := AffineMap.homothety_isOpenMap p t ht0.ne'
  have hDi : AffineMap.homothety p t '' interior C ⊆ interior D :=
    hopen.image_interior_subset C
  have hKD : K ⊆ interior D := by
    intro x hx
    apply hDi
    refine ⟨AffineMap.homothety p t⁻¹ x, htK x hx, ?_⟩
    exact (AffineEquiv.homothetyUnitsMulHom p (Units.mk0 t ht0.ne')).apply_symm_apply x
  refine ⟨D, hC.image (AffineMap.homothety_continuous p t),
    hc.affine_image _, ⟨AffineMap.homothety p t p, hDi ⟨p, hp, rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc.openSegment_interior_self_subset_interior hp hx
      (lineMap_mem_openSegment ℝ p x ⟨ht0, ht1⟩)
  · intro x hx
    by_contra hxu
    exact hx.2 (hKD ⟨hx.1, hxu⟩)
