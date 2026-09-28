import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeFaces

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

open Classical in


theorem isFinitePLBallPair_convex_coordinate_section
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {α β : Type} [Fintype α] [Fintype β]
    (C0 : Set V3) (hC : IsCompact C0) (hcv : Convex ℝ C0)
    (hC0 : (0 : V3) ∈ interior C0) (L : β → V3 →ₗ[ℝ] ℝ)
    (hrep : C0 = {x | ∀ j, L j x ≤ 1})
    (a : Y →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] Y) (hleft : Function.LeftInverse r a)
    (ha0 : a 0 = 0) (cuts : α → Y →ₗ[ℝ] ℝ)
    (hpos : ∃ v : Y, ∀ i, 0 < cuts i v) :
    IsFinitePLBallPair Y {w | a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w}
      {w | (a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w) ∧
        (a w ∈ frontier C0 ∨ ∃ i, cuts i w = 0)} := by
  classical
  have hright : LeftInvOn a r (range a) := by rintro _ ⟨w, rfl⟩; rw [hleft w]
  have hrange : range a = {x | a (r x) = x} :=
    Set.ext fun x => ⟨fun hx => hright hx, fun hx => ⟨r x, hx⟩⟩
  have hclosed : IsClosed (range a) := by
    rw [hrange]
    exact isClosed_eq (a.continuous.comp r.continuous) continuous_id
  have him : r '' (C0 ∩ range a) = a ⁻¹' C0 := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change a (r x) ∈ C0
      rw [hright hx.2]
      exact hx.1
    · exact fun hw => ⟨a w, ⟨hw, mem_range_self w⟩, hleft w⟩
  have hcpt : IsCompact (a ⁻¹' C0) := him ▸ (hC.inter_right hclosed).image r.continuous
  have hz : (0 : Y) ∈ interior (a ⁻¹' C0) := by
    apply preimage_interior_subset_interior_preimage a.continuous
    change a 0 ∈ interior C0
    rw [ha0]
    exact hC0
  obtain ⟨v, hv⟩ := hpos
  have hnonzero (i : α) : cuts i ≠ 0 := by
    intro he
    have h := hv i
    rw [he, LinearMap.zero_apply] at h
    exact (lt_irrefl _ h)
  let Q : Set Y := {w | ∀ i, 0 ≤ cuts i w}
  have hQc : IsClosed Q := by
    simp only [Q, ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (cuts i).continuous_of_finiteDimensional
  have hQi : interior Q = {w | ∀ i, 0 < cuts i w} := by
    have h := interior_finite_affine_halfspaces (fun i => -(cuts i).toAffineMap)
      (fun i => by simpa using hnonzero i)
    simpa only [Q, AffineMap.coe_neg, Pi.neg_apply, LinearMap.coe_toAffineMap,
      neg_nonpos, neg_lt_zero] using h
  let T0 := a ⁻¹' C0 ∩ Q
  have hTc : IsCompact T0 := hcpt.inter_right hQc
  have hTi : interior T0 = a ⁻¹' interior C0 ∩ {w | ∀ i, 0 < cuts i w} := by
    change interior (a ⁻¹' C0 ∩ Q) = _
    rw [interior_inter, a.interior_preimage_convex hcv ⟨0, ha0.symm ▸ hC0⟩, hQi]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hz
  let t := ε / (‖v‖ + 1)
  have ht : 0 < t := div_pos hε (by positivity)
  have htv : t * ‖v‖ < ε := by
    change ε / (‖v‖ + 1) * ‖v‖ < ε
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hw : t • v ∈ interior (a ⁻¹' C0) := by
    apply hball
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htv
  have hne : (interior T0).Nonempty := by
    refine ⟨t • v, ?_⟩
    change t • v ∈ interior (a ⁻¹' C0 ∩ Q)
    rw [interior_inter, hQi]
    exact ⟨hw, fun i => by simpa only [map_smul, smul_eq_mul] using mul_pos ht (hv i)⟩
  let forms : Finset (Y →ᵃ[ℝ] ℝ) :=
    Finset.univ.image (fun i => (L i).toAffineMap.comp a.toAffineMap - AffineMap.const ℝ Y 1) ∪
      Finset.univ.image (fun i => -(cuts i).toAffineMap)
  have hforms : T0 = {w | ∀ A ∈ forms, A w ≤ 0} := by
    ext w
    simp only [T0, mem_inter_iff, mem_preimage, hrep, Q, mem_ofPred_eq, forms,
      Finset.forall_mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      forall_exists_index, forall_apply_eq_imp_iff, AffineMap.coe_sub, Pi.sub_apply,
      AffineMap.comp_apply, AffineMap.const_apply, LinearMap.coe_toAffineMap,
      AffineMap.coe_neg, Pi.neg_apply, sub_nonpos, neg_nonpos]
    rfl
  have hb := isFinitePLBallPair_of_affine_halfspaces hTc forms hforms hne
  have hfront : frontier T0 = {w | w ∈ T0 ∧
      (a w ∈ frontier C0 ∨ ∃ i, cuts i w = 0)} := by
    rw [frontier, hTc.isClosed.closure_eq, hTi]
    ext w
    constructor
    · rintro ⟨hwT, hn⟩
      refine ⟨hwT, ?_⟩
      by_cases hi : a w ∈ interior C0
      · obtain ⟨i, hni⟩ := not_forall.mp (fun h => hn ⟨hi, h⟩)
        exact Or.inr ⟨i, le_antisymm (not_lt.mp hni) (hwT.2 i)⟩
      · exact Or.inl ⟨hC.isClosed.closure_eq.symm ▸ hwT.1, hi⟩
    · rintro ⟨hwT, hb | ⟨i, hi⟩⟩
      · exact ⟨hwT, fun h => hb.2 h.1⟩
      · exact ⟨hwT, fun h => (lt_irrefl (0 : ℝ)) (hi ▸ h.2 i)⟩
  rw [hfront] at hb
  convert hb using 1 <;> ext w <;>
    simp only [T0, Q, mem_inter_iff, mem_preimage, mem_ofPred_eq]

end PoincareConjecture.M76.Dehn

