import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain

def m64AnnulusRadialTranslation : LoopPlane := annulusPoint 0 1

local notation "v" => m64AnnulusRadialTranslation

def m64AnnulusLowerDomain : Set LoopPlane :=
  {p | 0 < p 0 ∧ p 0 < curvePeriod ∧ -1 < p 1 ∧ p 1 < 1}

def m64AnnulusLowerStrip : Set LoopPlane := (fun p => v + p) ⁻¹' S

theorem m64AnnulusLowerDomain_isOpen : IsOpen m64AnnulusLowerDomain := by
  have h0 : Continuous (fun p : LoopPlane => p 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
  have h1 : Continuous (fun p : LoopPlane => p 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  exact (isOpen_lt continuous_const h0).inter
    ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))

theorem m64AnnulusLowerStrip_isOpen : IsOpen m64AnnulusLowerStrip :=
  isOpen_interior.preimage (continuous_const.add continuous_id)

theorem m64AnnulusLowerStrip_coordinates (p : LoopPlane) :
    p ∈ m64AnnulusLowerStrip ↔
      0 < p 0 ∧ p 0 < curvePeriod ∧ -1 < p 1 ∧ p 1 < 0 := by
  change v + p ∈ S ↔ _
  rw [m64AnnulusInterior_coordinates]
  simp only [m64AnnulusRadialTranslation, annulusPoint, PiLp.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
  constructor
  · rintro ⟨h0, hP, hlow, hhigh⟩
    exact ⟨h0, hP, by linarith, by linarith⟩
  · rintro ⟨h0, hP, hlow, hhigh⟩
    exact ⟨h0, hP, by linarith, by linarith⟩

theorem m64AnnulusLower_rect_subset : S ⊆ m64AnnulusLowerDomain := by
  intro p hp
  obtain ⟨h0, hP, hlow, hhigh⟩ := (m64AnnulusInterior_coordinates p).mp hp
  exact ⟨h0, hP, by linarith, hhigh⟩

theorem m64AnnulusLower_strip_subset : m64AnnulusLowerStrip ⊆ m64AnnulusLowerDomain := by
  intro p hp
  obtain ⟨h0, hP, hlow, hhigh⟩ := (m64AnnulusLowerStrip_coordinates p).mp hp
  exact ⟨h0, hP, hlow, by linarith⟩

theorem m64AnnulusLower_disjoint : Disjoint S m64AnnulusLowerStrip := by
  apply disjoint_left.mpr
  intro p hp hq
  exact lt_asymm ((m64AnnulusInterior_coordinates p).mp hp).2.2.1
    ((m64AnnulusLowerStrip_coordinates p).mp hq).2.2.2

theorem m64_radial_line_null (c : ℝ) : volume {p : LoopPlane | p 1 = c} = 0 := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let q : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp _
  have hq : MeasurePreserving q volume volume := volume_preserving_finTwoArrow ℝ
  have hcomp : MeasurePreserving (q ∘ e) volume volume := hq.comp he
  let K : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ {c}
  have hK : NullMeasurableSet K volume := by measurability
  have hzero : volume K = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hpre := hcomp.measure_preimage hK
  have heq : (q ∘ e) ⁻¹' K = {p : LoopPlane | p 1 = c} := by
    ext p
    simp [q, e, K, MeasurableEquiv.finTwoArrow_apply]
  rw [← heq, hpre, hzero]

theorem m64AnnulusLowerDomain_ae_union :
    m64AnnulusLowerDomain =ᵐ[volume] (S ∪ m64AnnulusLowerStrip : Set LoopPlane) := by
  have hn : ∀ᵐ p : LoopPlane ∂volume, p 1 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_radial_line_null 0
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro h
    rcases lt_or_gt_of_ne hp with hl | hr
    · exact Or.inr ((m64AnnulusLowerStrip_coordinates p).mpr ⟨h.1, h.2.1, h.2.2.1, hl⟩)
    · exact Or.inl ((m64AnnulusInterior_coordinates p).mpr ⟨h.1, h.2.1, hr, h.2.2.2⟩)
  · rintro (h | h)
    · exact m64AnnulusLower_rect_subset h
    · exact m64AnnulusLower_strip_subset h

theorem m64AnnulusLower_translation_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => v + p)
      (volume.restrict m64AnnulusLowerStrip) (volume.restrict S) :=
  (measurePreserving_add_left (volume : Measure LoopPlane) v).restrict_preimage_emb
    (MeasurableEquiv.addLeft v).measurableEmbedding S

theorem m64AnnulusLower_negative_translation_measurePreserving :
    MeasurePreserving (fun p : LoopPlane => p - v)
      (volume.restrict S) (volume.restrict m64AnnulusLowerStrip) := by
  have h := (measurePreserving_add_left (volume : Measure LoopPlane) (-v)).restrict_preimage_emb
    (MeasurableEquiv.addLeft (-v)).measurableEmbedding m64AnnulusLowerStrip
  have hpre : (fun p : LoopPlane => -v + p) ⁻¹' m64AnnulusLowerStrip = S := by
    ext p
    simp only [m64AnnulusLowerStrip, mem_preimage, add_neg_cancel_left]
  rw [hpre] at h
  convert h using 1
  funext p
  abel

def m64AnnulusLowerExtend {E : Type*} (f g : LoopPlane → E) (p : LoopPlane) : E :=
  if p 1 < 0 then f (v + p) else g p

theorem m64AnnulusLowerExtend_right {E : Type*} (f g : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusLowerExtend f g p = g p := by
  simp only [m64AnnulusLowerExtend, not_lt.mpr ((m64AnnulusInterior_coordinates p).mp hp).2.2.1.le,
    ↓reduceIte]

theorem m64AnnulusLowerExtend_left {E : Type*} (f g : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ m64AnnulusLowerStrip) : m64AnnulusLowerExtend f g p = f (v + p) := by
  simp only [m64AnnulusLowerExtend, ((m64AnnulusLowerStrip_coordinates p).mp hp).2.2.2, ↓reduceIte]

theorem m64AnnulusLowerExtend_sub {E : Type*} (f g : LoopPlane → E)
    {p : LoopPlane} (hp : p ∈ S) : m64AnnulusLowerExtend f g (p - v) = f p := by
  have heq : v + (p - v) = p := by abel
  have hm : p - v ∈ m64AnnulusLowerStrip := by
    change v + (p - v) ∈ S
    simpa only [heq] using hp
  rw [m64AnnulusLowerExtend_left f g hm, heq]

theorem m64AnnulusLowerExtend_comp {E F : Type*} (f g : LoopPlane → E) (h : E → F) :
    h ∘ m64AnnulusLowerExtend f g = m64AnnulusLowerExtend (h ∘ f) (h ∘ g) := by
  funext p
  simp only [Function.comp_def, m64AnnulusLowerExtend]
  split_ifs <;> rfl

end PoincareConjecture
