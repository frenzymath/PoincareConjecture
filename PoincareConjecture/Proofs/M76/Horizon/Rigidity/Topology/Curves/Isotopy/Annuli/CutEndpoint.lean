import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.CutLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.RectangleIsotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.Lift



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => unitInterval
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Rect" => rectangle (4 * (8 : ℝ)) 1

private noncomputable def cutRectangleCoordinates : Rect ≃ₜ (I × I) where
  toFun x := (⟨((x : P2).2 + 1) / 2, by constructor <;> linarith [x.property.2.1, x.property.2.2]⟩,
    ⟨(x : P2).1 / 32, by constructor <;> linarith [x.property.1.1, x.property.1.2]⟩)
  invFun x := ⟨(32 * (x.2 : ℝ), 2 * (x.1 : ℝ) - 1),
    ⟨by constructor <;> linarith [x.2.property.1, x.2.property.2],
     by constructor <;> linarith [x.1.property.1, x.1.property.2]⟩⟩
  left_inv x := by apply Subtype.ext; ext <;> dsimp <;> ring
  right_inv x := by apply Prod.ext <;> apply Subtype.ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private noncomputable def cutRectangleProjection : C(Rect, Ann) :=
  ⟨fun x => annulusCylinderHomeomorph
    ((cutRectangleCoordinates x).1,
      ((32 * ((cutRectangleCoordinates x).2 : ℝ) : ℝ) : Circle)), by fun_prop⟩

private theorem cutRectangleProjection_val (x : Rect) :
    (cutRectangleProjection x : P2) = wrappedStripMap 8 x := by
  rw [show cutRectangleProjection x = annulusCylinderHomeomorph
    ((cutRectangleCoordinates x).1,
      ((32 * ((cutRectangleCoordinates x).2 : ℝ) : ℝ) : Circle)) from rfl,
    annulusCylinderHomeomorph_apply]
  change annulusMap 8 (by norm_num)
    (((32 * ((x : P2).1 / 32) : ℝ) : Circle), 2 * (((x : P2).2 + 1) / 2) - 1) = _
  rw [show 32 * ((x : P2).1 / 32) = (x : P2).1 by ring,
    show 2 * (((x : P2).2 + 1) / 2) - 1 = (x : P2).2 by ring]
  exact annulusMap_coe (by norm_num)
    (by have hh := abs_le.mpr x.property.2; linarith) x.property.1

theorem exists_finitePL_cut_rectangle_of_fixed_radial
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hrims : ∀ side z, G (annulusRimPoint side z) = annulusRimPoint side z)
    (hcut : ∀ t : I, G (annulusCylinderHomeomorph (t, 0)) =
      annulusCylinderHomeomorph (t, 0)) :
    ∃ e : Rect ≃ₜ Rect, e.IsFinitePL ∧
      (∀ x : Rect, (x : P2) ∈ frontier Rect → e x = x) ∧
      ∀ x : Rect, wrappedStripMap 8 (e x) =
        (G ⟨wrappedStripMap 8 x, (cutRectangleProjection_val x) ▸
          (cutRectangleProjection x).property⟩ : P2) := by
  classical
  let C := annulusCylinderHomeomorph
  let g := C.trans (G.trans C.symm)
  have hg0 (z : Circle) : g (0, z) = (0, z) := by
    change C.symm (G (annulusCylinderHomeomorph (0, z))) = _
    rw [annulusCylinderHomeomorph_zero, hrims, ← annulusCylinderHomeomorph_zero]
    exact C.symm_apply_apply _
  have hg1 (z : Circle) : g (1, z) = (1, z) := by
    change C.symm (G (annulusCylinderHomeomorph (1, z))) = _
    rw [annulusCylinderHomeomorph_one, hrims, ← annulusCylinderHomeomorph_one]
    exact C.symm_apply_apply _
  have hgc (t : I) : g (t, 0) = (t, 0) := by
    change C.symm (G (annulusCylinderHomeomorph (t, 0))) = _
    rw [hcut]
    exact C.symm_apply_apply _
  obtain ⟨f, hf, hfix⟩ := exists_cut_fixed_square_homeomorph g hg0 hg1 hgc
  let A := cutRectangleCoordinates
  let e : Rect ≃ₜ Rect := A.trans (f.trans A.symm)
  have hproject (x : Rect) : cutRectangleProjection (e x) = G (cutRectangleProjection x) := by
    change C ((A (A.symm (f (A x)))).1,
      ((32 * ((A (A.symm (f (A x)))).2 : ℝ) : ℝ) : Circle)) = _
    rw [A.apply_symm_apply, hf]
    change C (C.symm (G (cutRectangleProjection x))) = _
    exact C.apply_symm_apply _
  have hefix (x : Rect) (hx : (x : P2) ∈ frontier Rect) : e x = x := by
    have hx' : (x : P2).1 = 0 ∨ (x : P2).1 = 4 * 8 ∨
        (x : P2).2 = -1 ∨ (x : P2).2 = 1 := by
      change (x : P2) ∈ frontier (Icc (0 : ℝ) (4 * 8) ×ˢ Icc (-1 : ℝ) 1) at hx
      rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
        frontier_Icc (by norm_num : (0 : ℝ) ≤ 4 * 8),
        frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      simpa only [or_assoc] using
        (show ((x : P2).1 = 0 ∨ (x : P2).1 = 4 * 8) ∨
          ((x : P2).2 = -1 ∨ (x : P2).2 = 1) from
          hx.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1))
    have hface : (A x).1 = 0 ∨ (A x).1 = 1 ∨ (A x).2 = 0 ∨ (A x).2 = 1 := by
      rcases hx' with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by change (x : P2).1 / 32 = 0; rw [h]; norm_num))))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by change (x : P2).1 / 32 = 1; rw [h]; norm_num))))
      · exact Or.inl (Subtype.ext (by change ((x : P2).2 + 1) / 2 = 0; rw [h]; norm_num))
      · exact Or.inr (Or.inl (Subtype.ext (by change ((x : P2).2 + 1) / 2 = 1; rw [h]; norm_num)))
    change A.symm (f (A x)) = x
    rw [hfix _ hface, A.symm_apply_apply]
  let r : P2 → P2 := fun x => if hx : x ∈ Rect then e ⟨x, hx⟩ else 0
  have hr (x : Rect) : r x = (e x : P2) := by simp [r, x.property]
  have hw := finitePiecewiseAffineOn_wrappedStripMap
    (L := (8 : ℝ)) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨K, hK, hKs, _⟩ := hw
  have hcont : ContinuousOn r K.space := by
    rw [hKs]
    exact continuousOn_iff_continuous_domRestrict.mpr
      ((continuous_subtype_val.comp e.continuous).congr fun x => (hr x).symm)
  have hrPL : FinitePiecewiseAffineOn r Rect := by
    rw [← hKs]
    apply finitePiecewiseAffineOn_annular_real_lift (L := 8) (d := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) K hK hcont
    · intro x hx
      rw [hr ⟨x, hKs.subset hx⟩]
      have hh := (e ⟨x, hKs.subset hx⟩).property.2
      constructor <;> linarith [hh.1, hh.2]
    · obtain ⟨v, hv, hgv⟩ := hG
      have hcomp := hv.comp (finitePiecewiseAffineOn_wrappedStripMap
        (L := (8 : ℝ)) (d := 1) (by norm_num) (by norm_num))
        (show MapsTo (wrappedStripMap 8) Rect Ann from fun x hx =>
          (cutRectangleProjection_val ⟨x, hx⟩) ▸ (cutRectangleProjection ⟨x, hx⟩).property)
      apply (hKs.symm ▸ hcomp).congr
      intro x hx
      let y : Rect := ⟨x, hKs.subset hx⟩
      change v (wrappedStripMap 8 x) = _
      rw [← cutRectangleProjection_val y, ← hgv, ← hproject, cutRectangleProjection_val]
      change wrappedStripMap 8 (e y) = annulusMap 8 (by norm_num)
        (((r y).1 : Circle), (r y).2)
      rw [hr y]
      exact (annulusMap_coe (by norm_num)
        (by
          change 4 * |(e y : P2).2| < 8
          have hh := abs_le.mpr (e y).property.2
          linarith) (e y).property.1).symm
  refine ⟨e, ⟨r, hrPL, fun x => (hr x).symm⟩, hefix, ?_⟩
  intro x
  have h := congrArg Subtype.val (hproject x)
  rw [cutRectangleProjection_val] at h
  exact h.trans (congrArg (fun y : Ann => (G y : P2))
    (Subtype.ext (cutRectangleProjection_val x)))



theorem exists_joint_PL_annulus_isotopy_of_fixed_radial
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hrims : ∀ side z, G (annulusRimPoint side z) = annulusRimPoint side z)
    (hcut : ∀ t : I, G (annulusCylinderHomeomorph (t, 0)) =
      annulusCylinderHomeomorph (t, 0)) :
    ∃ (A : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      A 0 = Homeomorph.refl Ann ∧ A 1 = G ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun p : I × Ann => A p.1 p.2) ∧
      Continuous (fun p : I × Ann => (A p.1).symm p.2) ∧
      ∀ (t : I) (side : Bool) z,
        A t (annulusRimPoint side z) = annulusRimPoint side z := by
  obtain ⟨e, he, hfix, hq⟩ := exists_finitePL_cut_rectangle_of_fixed_radial G hG hrims hcut
  obtain ⟨A, F, Fi, hzero, hF, hFi, hFv, hFiv, hc, hci, hr, hend⟩ :=
    exists_joint_PL_annulus_isotopy_of_cut_rectangle e he hfix
  refine ⟨A, F, Fi, hzero, ?_, hF, hFi, hFv, hFiv, hc, hci, hr⟩
  apply Homeomorph.ext
  intro x
  obtain ⟨s, hs, hxs⟩ := exists_period_parameter_of_depth
    (L := 8) (d := 1) (by norm_num) (by norm_num) x
  let u : Icc (-1 : ℝ) 1 := ⟨depth 8 x, mem_squareAnnulus_iff_depth.mp x.property⟩
  let p : Rect := ⟨(s, u), hs, u.property⟩
  have hp : wrappedStripMap 8 p = (x : P2) := by
    rw [← annulusMap_coe (by norm_num)
      (show 4 * |(u : ℝ)| < 8 by have hh := abs_le.mpr u.property; linarith) hs]
    exact hxs.symm
  have harg : (⟨annulusMap 8 (by norm_num) ((s : Circle), u),
      _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : Ann) = x :=
    Subtype.ext hxs.symm
  have h := hend s hs u
  rw [harg] at h
  have htarget : annulusMap 8 (by norm_num)
      (((e p : P2).1 : Circle), (e p : P2).2) = wrappedStripMap 8 (e p) :=
    annulusMap_coe (by norm_num)
      (by have hh := abs_le.mpr (e p).property.2; linarith) (e p).property.1
  apply Subtype.ext
  exact h.trans (htarget.trans ((hq p).trans
    (congrArg (fun y : Ann => (G y : P2)) (Subtype.ext hp))))

end PoincareConjecture.M76.Dehn
