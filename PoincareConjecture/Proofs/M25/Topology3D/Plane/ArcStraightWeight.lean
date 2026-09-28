import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsertion
import PoincareConjecture.Proofs.M25.Topology3D.Plane.FamilyPersistence
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_polygonalArc_straight_weight {n : ℕ}
    (H : ℝ → Polygon E (n + 3)) (i : Fin (n + 1))
    (hH : ∀ j, ContDiff ℝ ∞ (fun t => H t j))
    {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d)
    (hgood : ∀ t ∈ Icc (a - d) (b + d), IsSimplePolygonalArc (H t))
    (hstraight : ∀ t ∈ Icc (a - d) (b + d),
      H t i.castSucc.succ ∈
        segment ℝ (H t (i.castSucc.succ.succAbove i.castSucc))
          (H t (i.castSucc.succ.succAbove i.succ))) :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ (∀ t, w t ∈ Ioo (0 : ℝ) 1) ∧
      ∀ t ∈ Icc a b,
        H t i.castSucc.succ =
          AffineMap.lineMap (H t (i.castSucc.succ.succAbove i.castSucc))
            (H t (i.castSucc.succ.succAbove i.succ)) (w t) := by
  classical
  let k : Fin (n + 3) := i.castSucc.succ
  let l : Fin (n + 3) := k.succAbove i.castSucc
  let r : Fin (n + 3) := k.succAbove i.succ
  let B := Module.finBasis ℝ E
  let y : ℝ → E := fun t => H t r - H t l
  let x : ℝ → E := fun t => H t k - H t l
  let D : ℝ → ℝ := fun t => ∑ j : Fin (Module.finrank ℝ E), (B.coord j (y t)) ^ 2
  let N : ℝ → ℝ := fun t => ∑ j : Fin (Module.finrank ℝ E),
    B.coord j (x t) * B.coord j (y t)
  have hil : l ≠ r := by
    intro h
    change k.succAbove i.castSucc = k.succAbove i.succ at h
    have hh : i.castSucc = i.succ :=
      (Fin.succAbove_right_injective (p := k)).eq_iff.mp h
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hyl (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) : y t ≠ 0 := by
    intro hy
    have hvl : H t r = H t l := sub_eq_zero.mp hy
    exact hil ((hgood t ht).vertices_injective hvl.symm)
  have hDpos (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) : 0 < D t := by
    have hc : ∃ j : Fin (Module.finrank ℝ E), B.coord j (y t) ≠ 0 := by
      by_contra hn
      apply hyl t ht
      apply B.forall_coord_eq_zero_iff.mp
      intro j
      by_contra hj
      exact hn ⟨j, hj⟩
    obtain ⟨j, hj⟩ := hc
    apply Finset.sum_pos' (fun j _ => sq_nonneg (B.coord j (y t)))
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hj⟩
  have hy_smooth : ContDiff ℝ ∞ y := by
    exact (hH r).sub (hH l)
  have hx_smooth : ContDiff ℝ ∞ x := by
    exact (hH k).sub (hH l)
  have hcoord_y (j : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (fun t => B.coord j (y t)) := by
    exact B.coord j |>.toContinuousLinearMap.contDiff.comp hy_smooth
  have hcoord_x (j : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (fun t => B.coord j (x t)) := by
    exact B.coord j |>.toContinuousLinearMap.contDiff.comp hx_smooth
  have hD_smooth : ContDiff ℝ ∞ D := by
    exact ContDiff.sum (fun j _ => (hcoord_y j).pow 2)
  have hN_smooth : ContDiff ℝ ∞ N := by
    exact ContDiff.sum (fun j _ => (hcoord_x j).mul (hcoord_y j))
  obtain ⟨θ, hθ, hθrange, hθid⟩ := exists_smooth_interval_clamp hab hd
  have hDθpos (z : ℝ) : 0 < D (θ z) := hDpos _ (hθrange z)
  have hcoeff (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) :
      ∃ c : ℝ, c ∈ Ioo (0 : ℝ) 1 ∧
        H t k = AffineMap.lineMap (H t l) (H t r) c := by
    have hseg := hstraight t ht
    rw [segment_eq_image_lineMap] at hseg
    obtain ⟨c, hc, hceq⟩ := hseg
    have hkl : k ≠ l := (Fin.succAbove_ne k i.castSucc).symm
    have hkr : k ≠ r := (Fin.succAbove_ne k i.succ).symm
    have hklv : H t k ≠ H t l := fun hh => hkl ((hgood t ht).vertices_injective hh)
    have hkrv : H t k ≠ H t r := fun hh => hkr ((hgood t ht).vertices_injective hh)
    have hc0 : c ≠ 0 := by
      intro hz
      apply hklv
      calc
        H t k = AffineMap.lineMap (H t l) (H t r) c := hceq.symm
        _ = H t l := by rw [hz, AffineMap.lineMap_apply_zero]
    have hc1 : c ≠ 1 := by
      intro hz
      apply hkrv
      calc
        H t k = AffineMap.lineMap (H t l) (H t r) c := hceq.symm
        _ = H t r := by rw [hz, AffineMap.lineMap_apply_one]
    have hcioo : c ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1⟩
    refine ⟨c, hcioo, hceq.symm⟩
  have hxy (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) :
      x t = (Classical.choose (hcoeff t ht)) • y t := by
    have heq := (Classical.choose_spec (hcoeff t ht)).2
    dsimp [x, y]
    calc
      H t k - H t l = AffineMap.lineMap (H t l) (H t r)
          (Classical.choose (hcoeff t ht)) - H t l := congrArg (fun v => v - H t l) heq
      _ = (Classical.choose (hcoeff t ht)) • (H t r - H t l) := by
        rw [AffineMap.lineMap_apply_module]
        module
  have hND (t : ℝ) (ht : t ∈ Icc (a - d) (b + d)) :
      N t = Classical.choose (hcoeff t ht) * D t := by
    have hxy' := hxy t ht
    have hcoord (j : Fin (Module.finrank ℝ E)) :
        B.coord j (x t) = Classical.choose (hcoeff t ht) * B.coord j (y t) := by
      rw [hxy']
      simp only [map_smul]
      ring
    dsimp [N, D]
    simp_rw [hcoord]
    calc
      (∑ j : Fin (Module.finrank ℝ E),
          Classical.choose (hcoeff t ht) * B.coord j (y t) * B.coord j (y t)) =
          ∑ j : Fin (Module.finrank ℝ E),
            Classical.choose (hcoeff t ht) * (B.coord j (y t)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = Classical.choose (hcoeff t ht) *
          ∑ j : Fin (Module.finrank ℝ E), (B.coord j (y t)) ^ 2 := by
            rw [Finset.mul_sum]
  let w : ℝ → ℝ := fun z => N (θ z) / D (θ z)
  have hw : ContDiff ℝ ∞ w := by
    apply hN_smooth.comp hθ |>.div (hD_smooth.comp hθ)
    exact fun z => ne_of_gt (hDθpos z)
  have hwval (z : ℝ) : w z ∈ Ioo (0 : ℝ) 1 := by
    have hc := (Classical.choose_spec (hcoeff (θ z) (hθrange z))).1
    have hND' := hND (θ z) (hθrange z)
    dsimp [w]
    rw [hND']
    have hquot : Classical.choose (hcoeff (θ z) (hθrange z)) * D (θ z) /
        D (θ z) = Classical.choose (hcoeff (θ z) (hθrange z)) := by
      exact (div_eq_iff (ne_of_gt (hDθpos z))).2 (by ring)
    rw [hquot]
    exact hc
  refine ⟨w, hw, hwval, ?_⟩
  intro t ht
  have hvalid : t ∈ Icc (a - d) (b + d) :=
    ⟨by linarith [ht.1, hd], by linarith [ht.2, hd]⟩
  have hceq := (Classical.choose_spec (hcoeff t hvalid)).2
  have htid := hθid t ht
  have hND' := hND t hvalid
  dsimp [w]
  rw [htid, hND']
  have hquot : Classical.choose (hcoeff t hvalid) * D t / D t =
      Classical.choose (hcoeff t hvalid) := by
    exact (div_eq_iff (ne_of_gt (hDpos t hvalid))).2 (by ring)
  rw [hquot]
  simpa only [k, l, r] using hceq

end PoincareConjecture.M25.Topology3D
