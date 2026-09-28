import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ClosedRectanglePhase








set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64




theorem closed_rectangle_phase_upper_integer {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (L : LoopPlane → ℝ) (hL : Continuous L)
    (hquot : ∀ p ∈ m64AnnulusDomain, C.quotient (L p) = f p)
    (L1 : ℝ → ℝ) (hL1 : Continuous L1)
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      C.quotient (L1 x) = f (annulusPoint x 1)) :
    ∃ k : ℤ, ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      L (annulusPoint x 1) = L1 x + k * circumference := by
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hd : ((L (annulusPoint 0 1) - L1 0 : ℝ) : AddCircle circumference) = 0 := by
    rw [AddCircle.coe_sub]
    apply sub_eq_zero.mpr
    exact (hquot _ ⟨le_rfl, hP, zero_le_one, le_rfl⟩).trans
      (hupper 0 ⟨le_rfl, hP⟩).symm
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff circumference).mp hd
  have hdiff := closed_rectangle_phase_boundary_difference C f L hL hquot
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) L1 hL1 hupper
  refine ⟨k, fun x hx => ?_⟩
  rw [hdiff x hx, ← hk]
  simp only [zsmul_eq_mul]




theorem closed_rectangle_phase_affine_seam {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (L : LoopPlane → ℝ) (hL : Continuous L)
    (hquot : ∀ p ∈ m64AnnulusDomain, C.quotient (L p) = f p)
    (hperiodic : ∀ s ∈ Icc (0 : ℝ) 1,
      f (annulusPoint curvePeriod s) = f (annulusPoint 0 s))
    {D : ℝ} (hbase : L (annulusPoint curvePeriod 0) = L (annulusPoint 0 0) + D) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      L (annulusPoint curvePeriod s) = L (annulusPoint 0 s) + D := by
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (L (annulusPoint curvePeriod s) : AddCircle circumference) =
        (L (annulusPoint 0 s) : AddCircle circumference) :=
    (hquot _ ⟨hP, le_rfl, hs.1, hs.2⟩).trans
      ((hperiodic s hs).trans (hquot _ ⟨le_rfl, hP, hs.1, hs.2⟩).symm)
  have hD : (D : AddCircle circumference) = 0 := by
    have hh := hq 0 ⟨le_rfl, zero_le_one⟩
    rw [hbase, AddCircle.coe_add] at hh
    exact add_left_cancel (hh.trans (add_zero _).symm)
  let R : ℝ → ℝ := fun s => projIcc (0 : ℝ) 1 (by norm_num) s
  have hR : Continuous R := continuous_subtype_val.comp continuous_projIcc
  have hRmem (s : ℝ) : R s ∈ Icc (0 : ℝ) 1 :=
    (projIcc (0 : ℝ) 1 zero_le_one s).property
  have hR0 : R 0 = 0 := congrArg Subtype.val
    (projIcc_of_mem zero_le_one (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩))
  have hright : Continuous (fun s : ℝ => annulusPoint curvePeriod (R s)) := by
    unfold annulusPoint
    fun_prop
  have hleft : Continuous (fun s : ℝ => annulusPoint 0 (R s)) := by
    unfold annulusPoint
    fun_prop
  have heq := (AddCircle.isCoveringMap_coe circumference).eq_of_comp_eq
    (hL.comp hright) ((hL.comp hleft).add continuous_const)
    (show (fun s : ℝ => (L (annulusPoint curvePeriod (R s)) : AddCircle circumference)) =
      (fun s : ℝ => ((L (annulusPoint 0 (R s)) + D : ℝ) : AddCircle circumference)) from by
        funext s
        rw [AddCircle.coe_add, hD, add_zero]
        exact hq (R s) (hRmem s))
    0 (by simpa only [Function.comp_apply, Pi.add_apply, hR0] using hbase)
  intro s hs
  simpa only [Function.comp_apply, Pi.add_apply, R,
    projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hs, Subtype.coe_mk] using congrFun heq s

end PoincareConjecture.M64
