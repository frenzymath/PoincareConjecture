import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.RimMatching
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.DepthHalves
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.LiftedRimPL



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem annular_rim_period_transfer (q : Circle → Circle)
    (hq : FinitePiecewiseAffineOn (fun s : ℝ =>
      (annulusRimPoint false (q ((32 * s : ℝ) : Circle)) : P2)) I) :
    ∀ b : Bool, FinitePiecewiseAffineOn (fun s : ℝ =>
      (annulusRimPoint b (q ((32 * s : ℝ) : Circle)) : P2)) I := by
  intro b
  cases b
  · exact hq
  · obtain ⟨R, ⟨f, hf, hfv⟩, _, hR⟩ :=
      _root_.Dehn.exists_square_annulus_depth_reflection (L := 8) (d := 1)
        (by norm_num) (by norm_num)
    apply (hf.comp hq (fun s _ => (annulusRimPoint false _).property)).congr
    intro s _
    let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
    let z := q ((32 * s : ℝ) : Circle)
    let t := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
    have ht : (t : ℝ) ∈ Icc 0 (4 * (8 : ℝ)) :=
      ⟨t.property.1, by simpa only [zero_add] using t.property.2.le⟩
    have htz : ((t : ℝ) : Circle) = z := AddCircle.coe_equivIco
    have h := hR t ht ⟨-1, by norm_num⟩
    rw [htz] at h
    exact (hfv (annulusRimPoint false z)).symm.trans
      (by simpa [annulusRimPoint] using h)

theorem exists_annular_rim_homeomorph (b : Bool) :
    ∃ H : Circle ≃ₜ range (fun z => (annulusRimPoint b z : P2)),
      ∀ z, (H z : P2) = annulusRimPoint b z := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hc := continuous_subtype_val.comp (continuous_annulusRimPoint b)
  have hi : Function.Injective (fun z => (annulusRimPoint b z : P2)) := by
    intro z w h
    exact injective_annulusRimPoint b (Subtype.ext h)
  exact ⟨(hc.isClosedEmbedding hi).isEmbedding.toHomeomorph, fun _ => rfl⟩

theorem exists_annular_chart_rim_homeomorph {T C : Set P2}
    (c : Ann ≃ₜ T) (b : Bool) (hC : C ⊆ T)
    (hmark : ∀ x : Ann, depth 8 (x : P2) = (if b then 1 else -1) ↔ (c x : P2) ∈ C) :
    ∃ H : Circle ≃ₜ C, ∀ z, (H z : P2) = c (annulusRimPoint b z) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let f : Circle → C := fun z =>
    ⟨c (annulusRimPoint b z), (hmark _).mp (depth_annulusRimPoint b z)⟩
  have hc : Continuous f :=
    (continuous_subtype_val.comp (c.continuous.comp (continuous_annulusRimPoint b))).subtype_mk _
  have hi : Function.Injective f := by
    intro z w h
    exact injective_annulusRimPoint b (c.injective
      (Subtype.ext (congrArg (fun x : C => (x : P2)) h)))
  have hs : Function.Surjective f := by
    intro y
    let x := c.symm ⟨y, hC y.property⟩
    have hx : depth 8 (x : P2) = (if b then 1 else -1) :=
      (hmark x).mpr (by simpa only [x, c.apply_symm_apply] using y.property)
    obtain ⟨z, hz⟩ := (range_annulusRimPoint b).symm.subset hx
    exact ⟨z, Subtype.ext (by change (c (annulusRimPoint b z) : P2) = y; rw [hz]; simp [x])⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi, hs⟩) hc,
    fun _ => rfl⟩

theorem exists_matched_annular_complements {T₀ T₁ C : Set P2}
    (outer : Ann ≃ₜ T₀) (inner : Ann ≃ₜ T₁)
    (houter : outer.IsFinitePL) (hinner : inner.IsFinitePL)
    (hout : T₀ ⊆ Ann) (hin : T₁ ⊆ Ann)
    (hC₀ : C ⊆ T₀) (hC₁ : C ⊆ T₁)
    (hB₀ : range (fun z => (annulusRimPoint false z : P2)) ⊆ T₀)
    (hB₁ : range (fun z => (annulusRimPoint true z : P2)) ⊆ T₁)
    (hoo : ∀ x : Ann, depth 8 (x : P2) = -1 ↔ depth 8 (outer x : P2) = -1)
    (hoi : ∀ x : Ann, depth 8 (x : P2) = 1 ↔ (outer x : P2) ∈ C)
    (hio : ∀ x : Ann, depth 8 (x : P2) = -1 ↔ (inner x : P2) ∈ C)
    (hii : ∀ x : Ann, depth 8 (x : P2) = 1 ↔ depth 8 (inner x : P2) = 1) :
    ∃ (O : Ann ≃ₜ T₀) (J : Ann ≃ₜ T₁) (gamma : Circle ≃ₜ C),
      O.IsFinitePL ∧ J.IsFinitePL ∧
      (∀ z : Circle, (O (annulusRimPoint false z) : P2) = annulusRimPoint false z) ∧
      (∀ z : Circle, (O (annulusRimPoint true z) : P2) = gamma z) ∧
      (∀ z : Circle, (J (annulusRimPoint false z) : P2) = gamma z) ∧
      ∀ z : Circle, (J (annulusRimPoint true z) : P2) = annulusRimPoint true z := by
  classical
  let rim (b : Bool) := range (fun z => (annulusRimPoint b z : P2))
  have hrim (b : Bool) (x : Ann) : depth 8 (x : P2) = (if b then 1 else -1) ↔
      (x : P2) ∈ rim b := by
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (range_annulusRimPoint b).symm.subset hx
      exact ⟨z, congrArg Subtype.val hz⟩
    · rintro ⟨z, hz⟩
      rw [← hz]
      exact depth_annulusRimPoint b z
  obtain ⟨R₀, hR₀⟩ := exists_annular_rim_homeomorph false
  obtain ⟨R₁, hR₁⟩ := exists_annular_rim_homeomorph true
  obtain ⟨P, hP⟩ := exists_annular_chart_rim_homeomorph outer true hC₀ hoi
  let B : Bool → Set P2 := fun b => if b then C else rim false
  let params : ∀ b, Circle ≃ₜ B b := fun b => by cases b; exact R₀; exact P
  have hB (b : Bool) : B b ⊆ T₀ := by cases b; exact hB₀; exact hC₀
  have hmarks (b : Bool) (x : Ann) : depth 8 (x : P2) = (if b then 1 else -1) ↔
      (outer x : P2) ∈ B b := by
    cases b
    · exact (hoo x).trans (hrim false ⟨outer x, hout (outer x).property⟩)
    · exact hoi x
  obtain ⟨ofun, hofun, hofunval⟩ := houter
  have hperiod (b : Bool) : FinitePiecewiseAffineOn
      (fun s : ℝ => (params b ((32 * s : ℝ) : Circle) : P2)) I := by
    cases b
    · exact (finitePiecewiseAffineOn_annulus_rim_period false).congr (fun _ _ => (hR₀ _).symm)
    · apply (hofun.comp (finitePiecewiseAffineOn_annulus_rim_period true)
        (fun s _ => (annulusRimPoint true _).property)).congr
      intro s _
      exact (hofunval _).symm.trans (hP _).symm
  have houtPL : outer.IsFinitePL := ⟨ofun, hofun, hofunval⟩
  obtain ⟨q, hq, hqPL⟩ := exists_finitePL_annulus_boundary_comparisons
    outer houtPL B hB params hperiod hmarks
  have hqperiod := annular_rim_period_transfer (q false) (hqPL false)
  obtain ⟨D, hD, hDv⟩ := exists_annulus_homotopic_rim_extension
    (fun _ => q false) (ContinuousMap.Homotopy.refl _) hqperiod
  let O := D.trans outer
  have hO : O.IsFinitePL := hD.trans houtPL
  have hOzero (z : Circle) : (O (annulusRimPoint false z) : P2) = annulusRimPoint false z := by
    change (outer (D (annulusRimPoint false z)) : P2) = _
    rw [hDv, hq false]
    exact hR₀ z
  have hOmark (x : Ann) : depth 8 (x : P2) = 1 ↔ (O x : P2) ∈ C := by
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := (range_annulusRimPoint true).symm.subset hx
      change (outer (D (annulusRimPoint true z)) : P2) ∈ C
      rw [hDv]
      exact (hoi _).mp (depth_annulusRimPoint true _)
    · intro hx
      have hxD := (hoi (D x)).mpr hx
      obtain ⟨z, hz⟩ := (range_annulusRimPoint true).symm.subset hxD
      have heq : x = annulusRimPoint true ((q false).symm z) := by
        apply D.injective
        rw [hDv, (q false).apply_symm_apply]
        exact hz.symm
      rw [heq]
      exact depth_annulusRimPoint true _
  obtain ⟨gamma, hgamma⟩ := exists_annular_chart_rim_homeomorph O true hC₀ hOmark
  let radial : C(Ann, Circle) :=
    ⟨fun x => (annulusCylinderHomeomorph.symm x).2,
      annulusCylinderHomeomorph.symm.continuous.snd⟩
  have hradial (b : Bool) (z : Circle) : radial (annulusRimPoint b z) = z := by
    cases b <;> change (annulusCylinderHomeomorph.symm (annulusRimPoint _ z)).2 = z
    · rw [← annulusCylinderHomeomorph_zero, annulusCylinderHomeomorph.symm_apply_apply]
    · rw [← annulusCylinderHomeomorph_one, annulusCylinderHomeomorph.symm_apply_apply]
  let gammaR : C(Circle, Circle) := ⟨fun z => radial ⟨gamma z, hout (hC₀ (gamma z).property)⟩,
    radial.continuous.comp ((continuous_subtype_val.comp gamma.continuous).subtype_mk _)⟩
  have Hgamma : Nonempty (gammaR.Homotopy (ContinuousMap.id Circle)) := by
    let c : C(Ann, Ann) := ⟨fun x => ⟨O x, hout (O x).property⟩,
      (continuous_subtype_val.comp O.continuous).subtype_mk _⟩
    let v : Bool → C(Circle, Circle) := fun b => if b then gammaR else ContinuousMap.id Circle
    have hv (b : Bool) (z : Circle) : radial (c (annulusRimPoint b z)) = v b z := by
      cases b
      · exact (congrArg radial (Subtype.ext (hOzero z))).trans (hradial false z)
      · exact congrArg radial (Subtype.ext (hgamma z).symm)
    exact ⟨(annulus_radial_rim_homotopy c radial v hv).symm⟩
  let B' : Bool → Set P2 := fun b => if b then rim true else C
  let params' : ∀ b, Circle ≃ₜ B' b := fun b => by cases b; exact gamma; exact R₁
  have hB' (b : Bool) : B' b ⊆ T₁ := by cases b; exact hC₁; exact hB₁
  have hmarks' (b : Bool) (x : Ann) : depth 8 (x : P2) = (if b then 1 else -1) ↔
      (inner x : P2) ∈ B' b := by
    cases b
    · exact hio x
    · exact (hii x).trans (hrim true ⟨inner x, hin (inner x).property⟩)
  obtain ⟨o, ho, hov⟩ := hO
  have hperiod' (b : Bool) : FinitePiecewiseAffineOn
      (fun s : ℝ => (params' b ((32 * s : ℝ) : Circle) : P2)) I := by
    cases b
    · apply (ho.comp (finitePiecewiseAffineOn_annulus_rim_period true)
        (fun s _ => (annulusRimPoint true _).property)).congr
      intro s _
      exact (hov _).symm.trans (hgamma _).symm
    · exact (finitePiecewiseAffineOn_annulus_rim_period true).congr (fun _ _ => (hR₁ _).symm)
  let radial' : C(T₁, Circle) := ⟨fun x => radial ⟨x, hin x.property⟩,
    radial.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hhom (b : Bool) : Nonempty
      ((⟨fun z => radial' ⟨params' b z, hB' b (params' b z).property⟩,
        radial'.continuous.comp ((continuous_subtype_val.comp (params' b).continuous).subtype_mk _)⟩ :
        C(Circle, Circle)).Homotopy (ContinuousMap.id Circle)) := by
    cases b
    · exact Hgamma
    · have heq : (⟨fun z => radial' ⟨R₁ z, hB₁ (R₁ z).property⟩,
          radial'.continuous.comp ((continuous_subtype_val.comp R₁.continuous).subtype_mk _)⟩ :
          C(Circle, Circle)) = ContinuousMap.id Circle := by
        ext z
        change radial ⟨R₁ z, _⟩ = z
        exact (congrArg radial (Subtype.ext (hR₁ z))).trans (hradial true z)
      exact heq.symm ▸ (⟨ContinuousMap.Homotopy.refl (ContinuousMap.id Circle)⟩ :
        Nonempty ((ContinuousMap.id Circle).Homotopy (ContinuousMap.id Circle)))
  obtain ⟨J, hJ, hJv⟩ := exists_annular_chart_prescribed_rims_of_radial_homotopies
    inner hinner B' hB' params' hperiod' hmarks' radial' hhom
  exact ⟨O, J, gamma, ⟨o, ho, hov⟩, hJ, hOzero, fun z => (hgamma z).symm,
    hJv false, fun z => (hJv true z).trans (hR₁ z)⟩

end PoincareConjecture.M76.Dehn
