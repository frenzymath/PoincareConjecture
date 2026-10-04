import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.NormalizedJacobian

/-!
# A genuine Jacobian cost for overlapping local sheets

Two distinct points of an open source with the same image produce a
nonempty open overlap. Apply the actual noninjective area inequality
separately to a closed ball about one point and to its complement in the
source. The target overlap contributes an additional positive area term.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareMT.M64Uniformization

local notation "Cover" => ℝ × ℝ

/-- A collision of an actual locally open differentiable planar map forces a nonempty open
overlap in the noninjective area inequality. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-unit-jacobian.md`. -/
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

/-- Unit Jacobian mass cannot support two local sheets when the actual image already has
area at least one. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit
project construction is recorded in `proof-work/tasks/M64/reports/annular-unit-jacobian.md`. -/
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

end PoincareMT.M64Uniformization
