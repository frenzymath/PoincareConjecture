import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.PairedExactMeridians
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ComplementaryCircleInterval
import PoincareConjecture.Proofs.M76.Rigidity.OriginalStripBoundaryTrace











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

variable {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
  {d : β → OpenPartialHomeomorph X V3} {phi : C(H, H)}
  {M : PairedMeridianHierarchy e d phi} {uv : ℝ × ℝ} (m : ExactSlabMeridian M uv)



noncomputable def frontierCylinderCoordinates :
    (Q × C) ≃ₜ frontier (sourceSlab M.eta uv.1 uv.2) :=
  (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short).trans m.frontierMap.symm



noncomputable def retainedCylinderParameter (z : V2 × ℝ) : X := by
  classical
  exact if hz : z.1 ∈ Q then
    (m.frontierCylinderCoordinates (⟨z.1, hz⟩, (z.2 : C)) : X) else 0

theorem retainedCylinderParameter_apply (z : V2) (hz : z ∈ Q) (t : ℝ) :
    m.retainedCylinderParameter (z, t) =
      (m.frontierCylinderCoordinates (⟨z, hz⟩, (t : C)) : X) := by
  classical
  simp only [retainedCylinderParameter, dif_pos hz]

theorem retainedCylinderParameter_mem_frontier (z : V2) (hz : z ∈ Q) (t : ℝ) :
    m.retainedCylinderParameter (z, t) ∈ frontier (sourceSlab M.eta uv.1 uv.2) := by
  rw [m.retainedCylinderParameter_apply z hz t]
  exact (m.frontierCylinderCoordinates (⟨z, hz⟩, (t : C))).property



theorem mem_retainedCylinderParameter_image_iff (J : Set ℝ)
    (x : frontier (sourceSlab M.eta uv.1 uv.2)) :
    (x : X) ∈ m.retainedCylinderParameter '' (Q ×ˢ J) ↔
      (m.frontierCylinderCoordinates.symm x).2 ∈ (fun t : ℝ => (t : C)) '' J := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [m.retainedCylinderParameter_apply z.1 hz.1 z.2] at hzx
    have heq : m.frontierCylinderCoordinates (⟨z.1, hz.1⟩, (z.2 : C)) = x :=
      Subtype.ext hzx
    refine ⟨z.2, hz.2, ?_⟩
    rw [← heq, Homeomorph.symm_apply_apply]
  · rintro ⟨t, ht, htx⟩
    let z := m.frontierCylinderCoordinates.symm x
    refine ⟨((z.1 : V2), t), ⟨z.1.property, ht⟩, ?_⟩
    rw [m.retainedCylinderParameter_apply (z.1 : V2) z.1.property t]
    change (m.frontierCylinderCoordinates (z.1, (t : C)) : X) = x
    change (t : C) = z.2 at htx
    rw [htx, Prod.eta]
    exact congrArg Subtype.val (m.frontierCylinderCoordinates.apply_symm_apply x)

theorem retainedCylinderParameter_eq_band (z : Q ×ˢ I) :
    m.retainedCylinderParameter z = m.bandParameter z := by
  rw [m.retainedCylinderParameter_apply z.val.1 z.property.1 z.val.2, ← m.band_exact z]
  change (m.frontierMap.symm
    (standardSlabBoundaryCoordinates uv.1 uv.2 m.ordered m.short
      (⟨z.val.1, z.property.1⟩, (z.val.2 : C))) : X) =
    (m.frontierMap.symm ⟨standardMeridianBandParameter uv.1 uv.2 z, _⟩ : X)
  apply congrArg Subtype.val
  apply congrArg m.frontierMap.symm
  apply Subtype.ext
  exact (standardMeridianBandParameter_eq_boundary uv.1 uv.2 m.ordered m.short
    ⟨z.val.1, z.property.1⟩ z.val.2).symm

theorem product_marks_retainedCylinder (z : V2) (hz : z ∈ Q) (t : ℝ) (ht : t ∈ I) :
    m.product.map (z, t) = m.retainedCylinderParameter (z, m.width * t) := by
  rw [m.product_marks z hz t ht]
  have hw : m.width * t ∈ I := by
    have hlo := mul_le_mul_of_nonneg_left ht.1 m.width_pos.le
    have hhi := mul_le_mul_of_nonneg_left ht.2 m.width_pos.le
    constructor <;> nlinarith [m.width_small]
  exact (m.retainedCylinderParameter_eq_band ⟨(z, m.width * t), hz, hw⟩).symm



theorem retainedCylinder_strip_trace :
    frontier (sourceSlab M.eta uv.1 uv.2) ∩ m.product.openStrip =
      m.retainedCylinderParameter '' (Q ×ˢ Ioo (-(m.width / 2)) (m.width / 2)) := by
  rw [m.product.frontier_inter_openStrip]
  have hI : Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ I :=
    fun _ ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z.1, m.width * z.2), ⟨hz.1, ?_, ?_⟩,
      (m.product_marks_retainedCylinder z.1 hz.1 z.2 (hI hz.2)).symm⟩
    · nlinarith [mul_lt_mul_of_pos_left hz.2.1 m.width_pos]
    · nlinarith [mul_lt_mul_of_pos_left hz.2.2 m.width_pos]
  · rintro ⟨z, hz, rfl⟩
    have ht : z.2 / m.width ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      constructor
      · apply (lt_div_iff₀ m.width_pos).mpr
        linarith [hz.2.1]
      · apply (div_lt_iff₀ m.width_pos).mpr
        linarith [hz.2.2]
    refine ⟨(z.1, z.2 / m.width), ⟨hz.1, ht⟩, ?_⟩
    rw [m.product_marks_retainedCylinder z.1 hz.1 _ (hI ht),
      mul_div_cancel₀ _ m.width_pos.ne']



theorem retainedCylinderParameter_injective :
    InjOn m.retainedCylinderParameter (Q ×ˢ Icc (m.width / 2) (p - m.width / 2)) := by
  intro z hz w hw hzw
  rw [m.retainedCylinderParameter_apply z.1 hz.1 z.2,
    m.retainedCylinderParameter_apply w.1 hw.1 w.2] at hzw
  have heq := m.frontierCylinderCoordinates.injective (Subtype.ext hzw)
  exact Prod.ext (congrArg (fun x : Q × C => (x.1 : V2)) heq)
    (AddCircle.injOn_coe_complementaryInterval (by linarith [m.width_pos]) hz.2 hw.2
      (congrArg Prod.snd heq))



theorem retainedCylinderParameter_image :
    m.retainedCylinderParameter '' (Q ×ˢ Icc (m.width / 2) (p - m.width / 2)) =
      frontier (sourceSlab M.eta uv.1 uv.2) \ m.product.openStrip := by
  have harc := @AddCircle.image_coe_complementaryInterval p _ (m.width / 2)
    (by linarith [m.width_pos] : 0 < m.width / 2)
    (by norm_num; linarith [m.width_small] : m.width / 2 < p / 2)
  have hdiff : frontier (sourceSlab M.eta uv.1 uv.2) \ m.product.openStrip =
      frontier (sourceSlab M.eta uv.1 uv.2) \
        (frontier (sourceSlab M.eta uv.1 uv.2) ∩ m.product.openStrip) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, m.retainedCylinder_strip_trace]
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hxf : x ∈ frontier (sourceSlab M.eta uv.1 uv.2) :=
      hzx ▸ m.retainedCylinderParameter_mem_frontier z.1 hz.1 z.2
    refine ⟨hxf, ?_⟩
    have hxclosed := (m.mem_retainedCylinderParameter_image_iff _ ⟨x, hxf⟩).mp ⟨z, hz, hzx⟩
    rw [harc] at hxclosed
    exact fun hopen => hxclosed ((m.mem_retainedCylinderParameter_image_iff _ ⟨x, hxf⟩).mp hopen)
  · rintro ⟨hxf, hnot⟩
    apply (m.mem_retainedCylinderParameter_image_iff _ ⟨x, hxf⟩).mpr
    rw [harc]
    exact fun hopen => hnot ((m.mem_retainedCylinderParameter_image_iff _ ⟨x, hxf⟩).mpr hopen)

theorem retainedCylinderParameter_lower (z : V2) (hz : z ∈ Q) :
    m.retainedCylinderParameter (z, m.width / 2) = m.product.map (z, (1 / 2 : ℝ)) := by
  simpa only [mul_one_div] using
    (m.product_marks_retainedCylinder z hz (1 / 2) (by norm_num)).symm

theorem retainedCylinderParameter_upper (z : V2) (hz : z ∈ Q) :
    m.retainedCylinderParameter (z, p - m.width / 2) = m.product.map (z, -(1 / 2 : ℝ)) := by
  rw [m.retainedCylinderParameter_apply z hz (p - m.width / 2),
    AddCircle.coe_period_sub, ← m.retainedCylinderParameter_apply z hz (-(m.width / 2))]
  simpa only [mul_neg, mul_one_div] using
    (m.product_marks_retainedCylinder z hz (-(1 / 2)) (by norm_num)).symm

end PoincareConjecture.M76.HamiltonIntervalTorus.ExactSlabMeridian
