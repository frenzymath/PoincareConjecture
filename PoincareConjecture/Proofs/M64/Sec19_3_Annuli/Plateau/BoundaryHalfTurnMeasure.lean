import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "a" => curvePeriod / 2
local notation "v" => annulusPoint (curvePeriod / 2) 0

def m64AnnulusHalfTurn (p : LoopPlane) : LoopPlane :=
  if p 0 < curvePeriod / 2 then p + annulusPoint (curvePeriod / 2) 0
  else p - annulusPoint (curvePeriod / 2) 0

def m64AnnulusHalfLeft : Set LoopPlane :=
  {p | 0 < p 0 ∧ p 0 < curvePeriod / 2 ∧ 0 < p 1 ∧ p 1 < 1}

def m64AnnulusHalfRight : Set LoopPlane :=
  {p | curvePeriod / 2 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1}

theorem m64AnnulusHalfTurn_measurable : Measurable m64AnnulusHalfTurn := by
  exact Measurable.ite (isOpen_lt
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous continuous_const).measurableSet
    (measurable_id.add measurable_const) (measurable_id.sub measurable_const)

theorem m64AnnulusHalfLeft_isOpen : IsOpen m64AnnulusHalfLeft := by
  exact (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).inter
    ((isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous continuous_const).inter
      ((isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).inter
        (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous continuous_const)))

theorem m64AnnulusHalfRight_isOpen : IsOpen m64AnnulusHalfRight := by
  exact (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).inter
    ((isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous continuous_const).inter
      ((isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).inter
        (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous continuous_const)))

theorem m64AnnulusHalf_disjoint : Disjoint m64AnnulusHalfLeft m64AnnulusHalfRight := by
  apply disjoint_left.mpr
  intro p hp hq
  exact lt_asymm hp.2.1 hq.1

theorem m64AnnulusHalf_ae_union :
    S =ᵐ[volume] (m64AnnulusHalfLeft ∪ m64AnnulusHalfRight : Set LoopPlane) := by
  have hn : ∀ᵐ p : LoopPlane ∂volume, p 0 ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_cut_line_null a
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  filter_upwards [hn] with p hp
  apply propext
  change p ∈ S ↔ p ∈ m64AnnulusHalfLeft ∪ m64AnnulusHalfRight
  rw [m64AnnulusInterior_coordinates]
  change _ ↔ (0 < p 0 ∧ p 0 < a ∧ 0 < p 1 ∧ p 1 < 1) ∨
    (a < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1)
  rcases lt_or_gt_of_ne hp with h | h <;> constructor <;> intro hs
  · exact Or.inl ⟨hs.1, h, hs.2.2⟩
  · rcases hs with hs | hs
    · exact ⟨hs.1, by linarith [hs.2.1], hs.2.2⟩
    · exact ⟨by linarith [hs.1], hs.2⟩
  · exact Or.inr ⟨h, hs.2⟩
  · rcases hs with hs | hs
    · exact ⟨hs.1, by linarith [hs.2.1], hs.2.2⟩
    · exact ⟨by linarith [hs.1], hs.2⟩

theorem m64AnnulusHalf_measure_decomposition :
    volume.restrict S = volume.restrict m64AnnulusHalfLeft +
      volume.restrict m64AnnulusHalfRight := by
  rw [Measure.restrict_congr_set m64AnnulusHalf_ae_union,
    Measure.restrict_union m64AnnulusHalf_disjoint m64AnnulusHalfRight_isOpen.measurableSet]

theorem m64AnnulusHalf_add_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => p + v)
      (volume.restrict m64AnnulusHalfLeft) (volume.restrict m64AnnulusHalfRight) := by
  have h := (measurePreserving_add_right (volume : Measure LoopPlane) v).restrict_preimage_emb
    (MeasurableEquiv.addRight v).measurableEmbedding m64AnnulusHalfRight
  have hpre : (fun p : LoopPlane => p + v) ⁻¹' m64AnnulusHalfRight =
      m64AnnulusHalfLeft := by
    ext p
    simp only [mem_preimage, m64AnnulusHalfRight, mem_ofPred_eq, PiLp.add_apply,
      annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, m64AnnulusHalfLeft]
    constructor <;> intro hp <;> exact ⟨by linarith [hp.1], by linarith [hp.2.1], hp.2.2⟩
  simpa only [hpre] using h

theorem m64AnnulusHalf_sub_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => p - v)
      (volume.restrict m64AnnulusHalfRight) (volume.restrict m64AnnulusHalfLeft) := by
  have h := (measurePreserving_add_right (volume : Measure LoopPlane) (-v)).restrict_preimage_emb
    (MeasurableEquiv.addRight (-v)).measurableEmbedding m64AnnulusHalfLeft
  have hpre : (fun p : LoopPlane => p + -v) ⁻¹' m64AnnulusHalfLeft =
      m64AnnulusHalfRight := by
    ext p
    simp only [mem_preimage, m64AnnulusHalfLeft, mem_ofPred_eq, PiLp.add_apply,
      PiLp.neg_apply, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_zero, add_zero, m64AnnulusHalfRight]
    constructor <;> intro hp <;> exact ⟨by linarith [hp.1], by linarith [hp.2.1], hp.2.2⟩
  simpa only [hpre, sub_eq_add_neg] using h

theorem m64AnnulusHalfTurn_measurePreserving :
    MeasurePreserving m64AnnulusHalfTurn (volume.restrict S) (volume.restrict S) := by
  refine ⟨m64AnnulusHalfTurn_measurable, ?_⟩
  rw [m64AnnulusHalf_measure_decomposition,
    Measure.map_add _ _ m64AnnulusHalfTurn_measurable]
  have hl : m64AnnulusHalfTurn =ᵐ[volume.restrict m64AnnulusHalfLeft]
      (fun p : LoopPlane => p + v) := by
    filter_upwards [ae_restrict_mem m64AnnulusHalfLeft_isOpen.measurableSet] with p hp
    exact if_pos hp.2.1
  have hr : m64AnnulusHalfTurn =ᵐ[volume.restrict m64AnnulusHalfRight]
      (fun p : LoopPlane => p - v) := by
    filter_upwards [ae_restrict_mem m64AnnulusHalfRight_isOpen.measurableSet] with p hp
    exact if_neg (not_lt.mpr hp.1.le)
  rw [Measure.map_congr hl, Measure.map_congr hr,
    m64AnnulusHalf_add_measurePreserving.map_eq, m64AnnulusHalf_sub_measurePreserving.map_eq,
    add_comm]

theorem m64AnnulusHalfTurn_memLp
    {E : Type*} [NormedAddCommGroup E] {q : ENNReal} {f : LoopPlane → E}
    (hf : MemLp f q (volume.restrict S)) :
    MemLp (f ∘ m64AnnulusHalfTurn) q (volume.restrict S) :=
  hf.comp_measurePreserving m64AnnulusHalfTurn_measurePreserving

theorem m64AnnulusHalfTurn_involutive_ae :
    ∀ᵐ p ∂volume.restrict S, m64AnnulusHalfTurn (m64AnnulusHalfTurn p) = p := by
  have hn : ∀ᵐ p : LoopPlane ∂volume, p 0 ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_cut_line_null a
  filter_upwards [ae_restrict_of_ae hn,
    ae_restrict_mem isOpen_interior.measurableSet] with p hp hS
  have hc := (m64AnnulusInterior_coordinates p).mp hS
  rcases lt_or_gt_of_ne hp with hl | hr
  · have hsum : ¬(p + v) 0 < a := by
      simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero]
      linarith [hc.1]
    simp only [m64AnnulusHalfTurn, if_pos hl, if_neg hsum, add_sub_cancel_right]
  · have hsub : (p - v) 0 < a := by
      simp only [PiLp.sub_apply, annulusPoint, Matrix.cons_val_zero]
      linarith [hc.2.1]
    simp only [m64AnnulusHalfTurn, if_neg (not_lt.mpr hr.le), if_pos hsub, sub_add_cancel]

theorem m64AnnulusHalfTurn_integral_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : LoopPlane → E} (hf : AEStronglyMeasurable f (volume.restrict S)) :
    (∫ p in S, f (m64AnnulusHalfTurn p)) = ∫ p in S, f p := by
  have hh : AEStronglyMeasurable f (Measure.map m64AnnulusHalfTurn (volume.restrict S)) := by
    rw [m64AnnulusHalfTurn_measurePreserving.map_eq]
    exact hf
  have h := integral_map m64AnnulusHalfTurn_measurable.aemeasurable hh
  rw [m64AnnulusHalfTurn_measurePreserving.map_eq] at h
  exact h.symm

theorem m64AnnulusHalfTurn_integral_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {phi : LoopPlane → ℝ} {f : LoopPlane → E}
    (hp : AEStronglyMeasurable phi (volume.restrict S))
    (hf : AEStronglyMeasurable f (volume.restrict S)) :
    (∫ p in S, phi p • f (m64AnnulusHalfTurn p)) =
      ∫ p in S, phi (m64AnnulusHalfTurn p) • f p := by
  have hpm := hp.comp_quasiMeasurePreserving
    m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving
  have hpair : AEStronglyMeasurable
      (fun p => phi (m64AnnulusHalfTurn p) • f p) (volume.restrict S) := hpm.smul hf
  rw [← m64AnnulusHalfTurn_integral_comp hpair]
  apply integral_congr_ae
  filter_upwards [m64AnnulusHalfTurn_involutive_ae] with p hp
  rw [hp]

end PoincareConjecture
