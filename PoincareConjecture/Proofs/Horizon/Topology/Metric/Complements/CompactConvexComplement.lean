import PoincareConjecture.Proofs.Horizon.Topology.Metric.Complements.ClosedBallComplement

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology ContinuousMap unitInterval

universe u

namespace Poincare.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]

theorem convex_complement_outward (K : Set E) (hK : Convex Real K)
    (x : E) (hx : x ∈ K) (y : E) (hy : y ∉ K) (a : Real) (ha : 1 ≤ a) :
    x + a • (y - x) ∉ K := by
  intro h
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hm := hK.add_smul_sub_mem hx h
    (show a⁻¹ ∈ Icc (0 : Real) 1 from
      ⟨inv_nonneg.mpr ha0.le, inv_le_one_of_one_le₀ ha⟩)
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul,
    add_sub_cancel] at hm
  exact hy hm

def compactConvexComplementInclusion (K : Set E) (x : E) (hx : x ∈ K) :
    C((Kᶜ : Set E), ({x}ᶜ : Set E)) :=
  ⟨fun y => ⟨y.val, fun h => y.property (h ▸ hx)⟩,
    continuous_subtype_val.subtype_mk _⟩

def compactConvexComplementPunctureHomotopyEquiv
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) : (Kᶜ : Set E) ≃ₕ ({x}ᶜ : Set E) := by
  let R := (hK.isBounded.subset_ball_lt 0 x).choose
  have hKR : K ⊆ ball x R := (hK.isBounded.subset_ball_lt 0 x).choose_spec.2
  let P : Set E := {x}ᶜ
  let O : Set E := Kᶜ
  have hn (y : P) : ‖y.val - x‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr y.property)
  have hnpos (y : P) : 0 < ‖y.val - x‖ := lt_of_le_of_ne (norm_nonneg _) (hn y).symm
  let alpha : C(P, Real) :=
    ⟨fun y => max 1 (R / ‖y.val - x‖),
      continuous_const.max
        (continuous_const.div (continuous_subtype_val.sub continuous_const).norm hn)⟩
  have ha (y : P) : 1 ≤ alpha y := le_max_left _ _
  have hj (y : P) : x + alpha y • (y.val - x) ∈ O := by
    intro hy
    have hnorm : ‖x + alpha y • (y.val - x) - x‖ < R := by
      simpa only [mem_ball, dist_eq_norm] using hKR hy
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (ha y))]
      at hnorm
    have hle : R ≤ alpha y * ‖y.val - x‖ :=
      (div_le_iff₀ (hnpos y)).mp (le_max_right 1 _)
    exact (not_lt_of_ge hle) hnorm
  let j : C(P, O) :=
    ⟨fun y => ⟨x + alpha y • (y.val - x), hj y⟩,
      (continuous_const.add (alpha.continuous.smul
        (continuous_subtype_val.sub continuous_const))).subtype_mk hj⟩
  let i : C(O, P) := compactConvexComplementInclusion K x hx
  let beta (z : unitInterval × P) : Real :=
    AffineMap.lineMap (alpha z.2) 1 (z.1 : Real)
  have hbeta : Continuous beta := by
    dsimp [beta]
    simp only [AffineMap.lineMap_apply_ring]
    fun_prop
  have hb (z : unitInterval × P) : 1 ≤ beta z :=
    (convex_Ici (1 : Real)).lineMap_mem (ha z.2)
      (show (1 : Real) ∈ Ici 1 from by simp) z.1.property
  let H : C(unitInterval × P, E) :=
    ⟨fun z => x + beta z • (z.2.val - x),
      continuous_const.add (hbeta.smul
        ((continuous_subtype_val.comp continuous_snd).sub continuous_const))⟩
  have hHP (z : unitInterval × P) : H z ∈ P := by
    intro h
    have hzero : beta z • (z.2.val - x) = 0 := by
      have he : x + beta z • (z.2.val - x) = x := h
      exact add_left_cancel (he.trans (add_zero x).symm)
    have hb0 : beta z ≠ 0 := (zero_lt_one.trans_le (hb z)).ne'
    exact (sub_ne_zero.mpr z.2.property) ((smul_eq_zero.mp hzero).resolve_left hb0)
  have hHO (t : unitInterval) (y : O) : H (t, i y) ∈ O :=
    convex_complement_outward K hconv x hx y.val y.property (beta (t, i y)) (hb _)
  have hH0 (y : P) : H (0, y) = (j y).val := by
    change x + AffineMap.lineMap (alpha y) 1 0 • (y.val - x) =
      x + alpha y • (y.val - x)
    rw [AffineMap.lineMap_apply_zero]
  have hH1 (y : P) : H (1, y) = y.val := by
    change x + AffineMap.lineMap (alpha y) 1 1 • (y.val - x) = y.val
    rw [AffineMap.lineMap_apply_one, one_smul, add_sub_cancel]
  let HO : (j.comp i).Homotopy (ContinuousMap.id O) :=
    { toFun := fun z => ⟨H (z.1, i z.2), hHO z.1 z.2⟩
      continuous_toFun :=
        (H.continuous.comp (continuous_fst.prodMk
          (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left y := Subtype.ext (hH0 (i y))
      map_one_left y := Subtype.ext (hH1 (i y)) }
  let HP : (i.comp j).Homotopy (ContinuousMap.id P) :=
    { toFun := fun z => ⟨H z, hHP z⟩
      continuous_toFun := H.continuous.subtype_mk hHP
      map_zero_left y := Subtype.ext (hH0 y)
      map_one_left y := Subtype.ext (hH1 y) }
  exact ⟨i, j, ⟨HO⟩, ⟨HP⟩⟩

theorem compactConvexComplementPunctureHomotopyEquiv_toFun
    (K : Set E) (hK : IsCompact K) (hconv : Convex Real K)
    (x : E) (hx : x ∈ K) :
    (compactConvexComplementPunctureHomotopyEquiv K hK hconv x hx).toFun =
      compactConvexComplementInclusion K x hx := by
  unfold compactConvexComplementPunctureHomotopyEquiv
  rfl

end Poincare.Topology
