import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCutSeparators




noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_band_physical_separator
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ} (hab : a < b)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra rb)
    (right : Bool) {v d : AnnulusCoordinates}
    (hdir : (if right then L (ub, wb) else L (ua, wa)) = d)
    (htangent : ∃ speed : ℝ, 0 < speed ∧
      v = speed • L (1, deriv f (if right then b else a)))
    (htrans : 0 < inner ℝ (quarterTurn v) d) :
    let p := L (if right then b else a, f (if right then b else a))
    ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ p ∈ W ∧ ell d = 0 ∧
      (if right then 0 < ell v else ell v < 0) ∧
      ∀ z ∈ B.carrier ∩ W, ell (z - p) ≤ 0 := by
  intro p
  let N := innerSL ℝ (-quarterTurn d)
  have hker : N d = 0 := by
    change inner ℝ (-quarterTurn d) d = 0
    rw [inner_neg_left, real_inner_comm, inner_quarterTurn_self, neg_zero]
  have hrot : inner ℝ (-quarterTurn d) v = inner ℝ (quarterTurn v) d := by
    have h := inner_quarterTurn_self (v + d)
    simp only [map_add, inner_add_left, inner_add_right, inner_quarterTurn_self] at h
    rw [inner_neg_left, real_inner_comm]
    have hc := real_inner_comm d (quarterTurn v)
    linarith
  have hNv : 0 < N v := by simpa only [N, innerSL_apply_apply, hrot] using htrans
  obtain ⟨speed, hspeed, hv⟩ := htangent
  have hpos : 0 < N (L (1, deriv f (if right then b else a))) := by
    rw [hv, map_smul, smul_eq_mul] at hNv
    exact (mul_pos_iff_of_pos_left hspeed).mp hNv
  obtain ⟨W, hW, hpW, hsep⟩ := m64Intrinsic_exists_band_cut_separator L hab B right N
    (hdir ▸ hker) hpos
  refine ⟨if right then N else -N, W, hW, hpW, ?_, ?_, hsep⟩
  · cases right <;> simp [hker]
  · cases right <;> simpa using hNv

end PoincareConjecture
