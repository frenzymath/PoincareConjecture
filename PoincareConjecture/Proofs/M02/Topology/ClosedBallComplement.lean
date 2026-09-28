import PoincareConjecture.Proofs.M02.Topology.SphereOpenCover
import Mathlib.Analysis.Convex.Basic









set_option autoImplicit false

open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

variable {E : Type u} [NormedAddCommGroup E]

theorem closedBallComplement_subset_puncture (c : E) (r : Real) (hr : 0 ≤ r) :
    (closedBall c r)ᶜ ⊆ ({c}ᶜ : Set E) := by
  apply Set.compl_subset_compl.mpr
  exact singleton_subset_iff.mpr (mem_closedBall_self hr)

def closedBallComplementInclusion (c : E) (r : Real) (hr : 0 ≤ r) :
    C(((closedBall c r)ᶜ : Set E), ({c}ᶜ : Set E)) :=
  ⟨fun x => ⟨x.val, closedBallComplement_subset_puncture c r hr x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

variable [NormedSpace Real E]

def closedBallComplementPunctureHomotopyEquiv (c : E) (r : Real) (hr : 0 ≤ r) :
    ((closedBall c r)ᶜ : Set E) ≃ₕ ({c}ᶜ : Set E) := by
  let P : Set E := {c}ᶜ
  let O : Set E := (closedBall c r)ᶜ
  let R : Real := r + 1
  have hR : r < R := by dsimp [R]; linarith
  have hRpos : 0 < R := hr.trans_lt hR
  have hn (x : P) : ‖x.val - c‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr x.property)
  let v : C(P, E) :=
    ⟨fun x => ‖x.val - c‖⁻¹ • (x.val - c),
      (((continuous_subtype_val.sub continuous_const).norm.inv₀ hn).smul
        (continuous_subtype_val.sub continuous_const))⟩
  have hv (x : P) : ‖v x‖ = 1 := by
    change ‖‖x.val - c‖⁻¹ • (x.val - c)‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hn x)]
  have hvrecover (x : P) : ‖x.val - c‖ • v x = x.val - c := by
    change ‖x.val - c‖ • (‖x.val - c‖⁻¹ • (x.val - c)) = x.val - c
    rw [smul_smul, mul_inv_cancel₀ (hn x), one_smul]
  have hj (x : P) : c + R • v x ∈ O := by
    change ¬dist (c + R • v x) c ≤ r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hRpos.le, hv, mul_one]
    exact not_le_of_gt hR
  let j : C(P, O) :=
    ⟨fun x => ⟨c + R • v x, hj x⟩,
      (continuous_const.add (continuous_const.smul v.continuous)).subtype_mk hj⟩
  let i : C(O, P) := closedBallComplementInclusion c r hr
  let radius (z : unitInterval × P) : Real :=
    AffineMap.lineMap R ‖z.2.val - c‖ (z.1 : Real)
  have hrad : Continuous radius := by
    dsimp [radius]
    simp only [AffineMap.lineMap_apply_ring]
    fun_prop
  have hradpos (z : unitInterval × P) : 0 < radius z :=
    (convex_Ioi (0 : Real)).lineMap_mem hRpos
      (norm_pos_iff.mpr (sub_ne_zero.mpr z.2.property)) z.1.property
  let K : C(unitInterval × P, E) :=
    ⟨fun z => c + radius z • v z.2,
      continuous_const.add (hrad.smul (v.continuous.comp continuous_snd))⟩
  have hKnorm (z : unitInterval × P) : ‖K z - c‖ = radius z := by
    change ‖c + radius z • v z.2 - c‖ = radius z
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hradpos z).le,
      hv, mul_one]
  have hKpoint (z : unitInterval × P) : K z ∈ P := by
    intro h
    have he : K z = c := h
    have hnorm := hKnorm z
    rw [he, sub_self, norm_zero] at hnorm
    exact (ne_of_gt (hradpos z)) hnorm.symm
  have hKout (t : unitInterval) (x : O) : K (t, i x) ∈ O := by
    have hx : r < ‖(i x).val - c‖ := by
      change r < ‖x.val - c‖
      have hx' : ¬dist x.val c ≤ r := x.property
      simpa only [not_le, dist_eq_norm] using hx'
    have hradius : r < radius (t, i x) :=
      (convex_Ioi r).lineMap_mem hR hx t.property
    change ¬dist (K (t, i x)) c ≤ r
    rw [dist_eq_norm, hKnorm]
    exact not_le_of_gt hradius
  have hK0 (x : P) : K (0, x) = (j x).val := by
    change c + AffineMap.lineMap R ‖x.val - c‖ 0 • v x = c + R • v x
    rw [AffineMap.lineMap_apply_zero]
  have hK1 (x : P) : K (1, x) = x.val := by
    change c + AffineMap.lineMap R ‖x.val - c‖ 1 • v x = x.val
    rw [AffineMap.lineMap_apply_one, hvrecover]
    abel
  let HO : (j.comp i).Homotopy (ContinuousMap.id O) :=
    { toFun := fun z => ⟨K (z.1, i z.2), hKout z.1 z.2⟩
      continuous_toFun :=
        (K.continuous.comp (continuous_fst.prodMk
          (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left x := Subtype.ext (hK0 (i x))
      map_one_left x := Subtype.ext (hK1 (i x)) }
  let HP : (i.comp j).Homotopy (ContinuousMap.id P) :=
    { toFun := fun z => ⟨K z, hKpoint z⟩
      continuous_toFun := K.continuous.subtype_mk hKpoint
      map_zero_left x := Subtype.ext (hK0 x)
      map_one_left x := Subtype.ext (hK1 x) }
  exact ⟨i, j, ⟨HO⟩, ⟨HP⟩⟩

theorem closedBallComplementPunctureHomotopyEquiv_toFun
    (c : E) (r : Real) (hr : 0 ≤ r) :
    (closedBallComplementPunctureHomotopyEquiv c r hr).toFun =
      closedBallComplementInclusion c r hr := rfl

def punctureTranslationHomeomorph (c : E) :
    ({c}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) := by
  have hf (x : ({c}ᶜ : Set E)) : x.val - c ∈ ({0}ᶜ : Set E) :=
    sub_ne_zero.mpr x.property
  have hg (x : ({0}ᶜ : Set E)) : c + x.val ∈ ({c}ᶜ : Set E) := by
    intro h
    have he : c + x.val = c := h
    exact x.property (add_left_cancel (he.trans (add_zero c).symm))
  exact {
    toFun := fun x => ⟨x.val - c, hf x⟩
    invFun := fun x => ⟨c + x.val, hg x⟩
    left_inv := fun x => Subtype.ext (by dsimp; abel)
    right_inv := fun x => Subtype.ext (by dsimp; abel)
    continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk hf
    continuous_invFun := (continuous_const.add continuous_subtype_val).subtype_mk hg }

def closedBallComplementSphereHomotopyEquiv (c : E) (r : Real) (hr : 0 ≤ r) :
    ((closedBall c r)ᶜ : Set E) ≃ₕ sphere (0 : E) 1 :=
  (closedBallComplementPunctureHomotopyEquiv c r hr).trans
    ((punctureTranslationHomeomorph c).toHomotopyEquiv.trans
      (puncturedSpaceSphereHomotopyEquiv E))

end

end PoincareConjecture.Proofs.M02.Topology
