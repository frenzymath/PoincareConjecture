import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarNormalizedJacobian













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ





theorem scalar_area_overlap_of_collision {f : Cover → Cover} {U : Set Cover}
    (hU : IsOpen U) (hd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    (ho : ∀ z ∈ U, 𝓝 (f z) ≤ map f (𝓝 z))
    {x y : Cover} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) (hfxy : f x = f y) :
    ∃ W : Set Cover, IsOpen W ∧ W.Nonempty ∧
      volume (f '' U) + volume W ≤ ∫⁻ z in U, ENNReal.ofReal |(fderiv ℝ f z).det| := by
  have himageOpen {S : Set Cover} (hS : IsOpen S) (hsub : S ⊆ U) : IsOpen (f '' S) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact ho z (hsub hz) (Filter.image_mem_map (hS.mem_nhds hz))
  obtain ⟨r, hr, hKsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (hU.mem_nhds hx) (isOpen_compl_singleton.mem_nhds hxy))
  let K := Metric.closedBall x r
  let R := U \ K
  have hKsub : K ⊆ U := fun z hz => (hKsmall hz).1
  have hyK : y ∉ K := by
    intro hyK
    exact (hKsmall hyK).2 rfl
  have hR : IsOpen R := hU.sdiff Metric.isClosed_closedBall
  have hRsub : R ⊆ U := sdiff_subset
  have hIR : IsOpen (f '' R) := himageOpen hR hRsub
  let W := (f '' Metric.ball x r) ∩ (f '' R)
  have hW : IsOpen W := (himageOpen Metric.isOpen_ball
    (Metric.ball_subset_closedBall.trans hKsub)).inter hIR
  have hWne : W.Nonempty := ⟨f x, ⟨x, Metric.mem_ball_self hr, rfl⟩,
    ⟨y, ⟨hy, hyK⟩, hfxy.symm⟩⟩
  have hWsub : W ⊆ (f '' K) ∩ (f '' R) :=
    inter_subset_inter (image_mono Metric.ball_subset_closedBall) subset_rfl
  have hpartition : K ∪ R = U := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact hKsub hz
      · exact hz.1
    · intro hz
      by_cases hzK : z ∈ K
      · exact Or.inl hzK
      · exact Or.inr ⟨hz, hzK⟩
  have htarget : f '' U = (f '' K) ∪ (f '' R) := by rw [← image_union, hpartition]
  have hareaK := addHaar_image_le_lintegral_abs_det_fderiv volume
    (show MeasurableSet K from Metric.isClosed_closedBall.measurableSet)
    (fun z hz => (hd z (hKsub hz)).hasFDerivAt.hasFDerivWithinAt)
  have hareaR := addHaar_image_le_lintegral_abs_det_fderiv volume hR.measurableSet
    (fun z hz => (hd z (hRsub hz)).hasFDerivAt.hasFDerivWithinAt)
  have hdisjoint : Disjoint K R := by
    apply disjoint_left.mpr
    intro z hzK hzR
    exact hzR.2 hzK
  refine ⟨W, hW, hWne, ?_⟩
  calc
    volume (f '' U) + volume W ≤
        volume ((f '' K) ∪ (f '' R)) + volume ((f '' K) ∩ (f '' R)) := by
      rw [← htarget]
      have hmu : volume W ≤ volume ((f '' K) ∩ (f '' R)) := measure_mono hWsub
      exact add_le_add le_rfl hmu
    _ = volume (f '' K) + volume (f '' R) := measure_union_add_inter _ hIR.measurableSet
    _ ≤ (∫⁻ z in K, ENNReal.ofReal |(fderiv ℝ f z).det|) +
        ∫⁻ z in R, ENNReal.ofReal |(fderiv ℝ f z).det| := add_le_add hareaK hareaR
    _ = ∫⁻ z in U, ENNReal.ofReal |(fderiv ℝ f z).det| := by
      rw [← lintegral_union hR.measurableSet hdisjoint, hpartition]




theorem scalar_injOn_of_unit_jacobian_and_image_area {f : Cover → Cover} {U : Set Cover}
    (hU : IsOpen U) (hd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    (ho : ∀ z ∈ U, 𝓝 (f z) ≤ map f (𝓝 z))
    (himage : 1 ≤ volume (f '' U))
    (hmass : (∫⁻ z in U, ENNReal.ofReal |(fderiv ℝ f z).det|) ≤ 1) : InjOn f U := by
  intro x hx y hy hfxy
  by_contra hxy
  obtain ⟨W, hW, hWne, hoverlap⟩ := scalar_area_overlap_of_collision hU hd ho hx hy hxy hfxy
  have hpositive : 0 < volume W := hW.measure_pos volume hWne
  have hsum : (1 : ℝ≥0∞) + volume W ≤ 1 + 0 := by
    simpa only [add_zero] using
      (add_le_add himage (le_refl (volume W))).trans (hoverlap.trans hmass)
  have hzero : volume W ≤ 0 := (ENNReal.add_le_add_iff_left (by norm_num)).mp hsum
  exact hpositive.not_ge hzero

end PoincareConjecture.M64Uniformization
