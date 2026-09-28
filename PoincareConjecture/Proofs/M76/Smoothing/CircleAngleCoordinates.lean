import PoincareConjecture.Proofs.M76.Smoothing.CircleGapVertices










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}




def shortArcAngleSpace (n : ℕ) (theta : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {a | a 0 = 0 ∧ a 1 = theta ∧
    (∀ i : Fin (n + 2), a i.succ - a i.castSucc ∈ Ioo (0 : ℝ) Real.pi) ∧
    2 * Real.pi - a (Fin.last (n + 2)) ∈ Ioo (0 : ℝ) Real.pi}



noncomputable def angleGaps (a : Fin (n + 3) → ℝ) : Fin (n + 3) → ℝ :=
  Fin.lastCases (2 * Real.pi - a (Fin.last (n + 2)))
    (fun i => a i.succ - a i.castSucc)



theorem gapAngle_last_add (w : Fin (n + 3) → ℝ) :
    gapAngle w (Fin.last (n + 2)) + w (Fin.last (n + 2)) = ∑ i, w i := by
  have hs : Finset.univ = insert (Fin.last (n + 2))
      (Finset.Iio (Fin.last (n + 2))) := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio, true_iff,
      Fin.ext_iff, Fin.lt_def, Fin.val_last]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  exact add_comm _ _



theorem angleGaps_gapAngle (w : Fin (n + 3) → ℝ) (hw : (∑ i, w i) = 2 * Real.pi) :
    angleGaps (gapAngle w) = w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [angleGaps, Fin.lastCases_last]
    linarith [gapAngle_last_add w]
  · simp [angleGaps, gapAngle_succ]



theorem gapAngle_angleGaps (a : Fin (n + 3) → ℝ) (i : Fin (n + 3)) :
    gapAngle (angleGaps a) i = a i - a 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      rw [gapAngle_succ, ih]
      simp only [angleGaps, Fin.lastCases_castSucc]
      ring



theorem sum_angleGaps (a : Fin (n + 3) → ℝ) :
    (∑ i, angleGaps a i) = 2 * Real.pi - a 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [angleGaps, Fin.lastCases_castSucc, Fin.lastCases_last,
    Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ a
  have hlast := Fin.sum_univ_castSucc a
  linarith



theorem gapAngle_mem_shortArcAngleSpace {w : Fin (n + 3) → ℝ}
    (hw : w ∈ shortArcGapSpace n theta) : gapAngle w ∈ shortArcAngleSpace n theta := by
  refine ⟨gapAngle_zero w, gapAngle_one hw, ?_, ?_⟩
  · intro i
    simpa [gapAngle_succ] using hw.1 i.castSucc
  · have hlast : 2 * Real.pi - gapAngle w (Fin.last (n + 2)) =
        w (Fin.last (n + 2)) := by linarith [gapAngle_last_add w, hw.2.1]
    rw [hlast]
    exact hw.1 _



theorem angleGaps_mem_shortArcGapSpace {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) : angleGaps a ∈ shortArcGapSpace n theta := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [angleGaps, Fin.lastCases_last] using ha.2.2.2
    · simpa only [angleGaps, Fin.lastCases_castSucc] using ha.2.2.1 j
  · rw [sum_angleGaps, ha.1, sub_zero]
  · change angleGaps a (Fin.castSucc (0 : Fin (n + 2))) = theta
    rw [angleGaps, Fin.lastCases_castSucc]
    simpa using sub_eq_iff_eq_add.mpr (show a 1 = theta + a 0 by rw [ha.1, ha.2.1, add_zero])



theorem continuous_angleGaps :
    Continuous (angleGaps : (Fin (n + 3) → ℝ) → Fin (n + 3) → ℝ) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [angleGaps, Fin.lastCases_last]
    exact continuous_const.sub (continuous_apply _)
  · simp only [angleGaps, Fin.lastCases_castSucc]
    exact (continuous_apply _).sub (continuous_apply _)



noncomputable def gapAngleHomeomorph (n : ℕ) (theta : ℝ) :
    shortArcGapSpace n theta ≃ₜ shortArcAngleSpace n theta where
  toFun w := ⟨gapAngle w, gapAngle_mem_shortArcAngleSpace w.property⟩
  invFun a := ⟨angleGaps a, angleGaps_mem_shortArcGapSpace a.property⟩
  left_inv w := by
    apply Subtype.ext
    exact angleGaps_gapAngle w.val w.property.2.1
  right_inv a := Subtype.ext (funext fun i => by
    change gapAngle (angleGaps a.val) i = a.val i
    rw [gapAngle_angleGaps, a.property.1, sub_zero])
  continuous_toFun := (continuous_pi (fun i =>
    (continuous_gapAngle i).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (continuous_angleGaps.comp continuous_subtype_val).subtype_mk _



theorem strictMono_shortArcAngles {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) : StrictMono a := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  exact sub_pos.mp (ha.2.2.1 i).1



theorem shortArcAngles_mem_Ico {a : Fin (n + 3) → ℝ}
    (ha : a ∈ shortArcAngleSpace n theta) (i : Fin (n + 3)) :
    a i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  have hmono := (strictMono_shortArcAngles ha).monotone
  constructor
  · simpa [ha.1] using hmono (Fin.zero_le i)
  · have hle := hmono (Fin.le_last i)
    linarith [ha.2.2.2.1]

end PoincareConjecture.M76.Smoothing
