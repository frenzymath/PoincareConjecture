import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.KernelTransport
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.RicciFlow.Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma eventually_finrank_kernel_le
    {X : Type*} [TopologicalSpace X] {A : X → E →L[ℝ] E} {S : Set X} {p : X}
    (hA : ContinuousWithinAt A S p) (hsym : (A p).toLinearMap.IsSymmetric) :
    ∀ᶠ q in 𝓝[S] p, Module.finrank ℝ (A q).ker ≤ Module.finrank ℝ (A p).ker := by
  let K := (A p).ker
  have hB : (A p + K.starProjection).IsInvertible :=
    isInvertible_add_kernel_projection (A p) hsym
  have hnear : ∀ᶠ q in 𝓝[S] p, IsUnit (A q + K.starProjection) :=
    (hA.add_const K.starProjection).eventually
      (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hB.bijective))
  filter_upwards [hnear] with q hq
  let L : (A q).ker →ₗ[ℝ] K :=
    K.orthogonalProjectionOnto.toLinearMap.comp (A q).ker.subtype
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro v w hvw
  apply Subtype.ext
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp hq).1
  change A q v + K.starProjection v = A q w + K.starProjection w
  rw [show A q v = 0 from v.property, show A q w = 0 from w.property, zero_add, zero_add]
  exact congrArg Subtype.val hvw

theorem kernel_antitone_of_derivative_annihilates
    {A D : ℝ → E →L[ℝ] E} {a b : ℝ}
    (hA : ∀ t ∈ Icc a b, HasDerivWithinAt A (D t) (Icc a b) t)
    (hsym : ∀ t ∈ Icc a b, (A t).toLinearMap.IsSymmetric)
    (hdim : AntitoneOn (fun t => Module.finrank ℝ (A t).ker) (Icc a b))
    (hann : ∀ t ∈ Icc a b, ∀ v, A t v = 0 → D t v = 0) :
    AntitoneOn (fun t => (A t).ker) (Icc a b) := by
  have hlocal (t : ℝ) (ht : t ∈ Icc a b) :
      ∃ r > 0, ∀ s ∈ Icc a t, t - r < s → (A s).ker = (A t).ker := by
    have hnear := eventually_finrank_kernel_le (hA t ht).continuousWithinAt (hsym t ht)
    obtain ⟨r, hr, hrad⟩ := Metric.mem_nhdsWithin_iff.mp hnear
    refine ⟨r, hr, ?_⟩
    intro s hs hst
    by_cases heq : s = t
    · simp [heq]
    have hlt : s < t := lt_of_le_of_ne hs.2 heq
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    apply kernel_eq_of_derivative_annihilates (k := Module.finrank ℝ (A t).ker)
      (convex_Icc s t) (uniqueDiffOn_Icc hlt)
      (fun q hq => (hA q (hsub hq)).mono hsub)
      (fun q hq => hsym q (hsub hq)) _ (fun q hq => hann q (hsub hq))
      (left_mem_Icc.mpr hs.2) (right_mem_Icc.mpr hs.2)
    intro q hq
    apply le_antisymm
    · apply hrad
      refine ⟨?_, hsub hq⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hq.2)]
      linarith [hq.1]
    · exact hdim (hsub hq) ht hq.2
  intro s hs t ht hst v hv
  let S := {q : ℝ | A q v = 0}
  have hcont : ContinuousOn (fun q => A q v) (Icc s t) :=
    fun q hq => ((hA q (Icc_subset_Icc hs.1 ht.2 hq)).continuousWithinAt.clm_apply
      continuousWithinAt_const).mono (Icc_subset_Icc hs.1 ht.2)
  have hclosed : IsClosed (S ∩ Icc s t) := by
    obtain ⟨C, hC, heq⟩ := continuousOn_iff_isClosed.mp hcont {0} isClosed_singleton
    change IsClosed (((fun q => A q v) ⁻¹' {0}) ∩ Icc s t)
    rw [heq]
    exact hC.inter isClosed_Icc
  apply hclosed.mem_of_ge_of_forall_exists_lt hv hst
  intro q hq
  obtain ⟨r, hr, hrad⟩ := hlocal q ⟨hs.1.trans hq.2.1.le, hq.2.2.trans ht.2⟩
  obtain ⟨z, hz₁, hz₂⟩ := exists_between (max_lt hq.2.1 (sub_lt_self q hr))
  refine ⟨z, ?_, le_of_lt ((le_max_left s (q - r)).trans_lt hz₁), hz₂⟩
  change v ∈ (A z).ker
  rw [hrad z ⟨hs.1.trans (le_max_left s (q - r) |>.trans hz₁.le), hz₂.le⟩
    ((le_max_right s (q - r)).trans_lt hz₁)]
  exact hq.1

end Poincare.RicciFlow.Splitting
