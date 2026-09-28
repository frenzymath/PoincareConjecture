import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseLift

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

private def clampAngular (x : ℝ) : ℝ := max 0 (min curvePeriod x)

private def clampRadial (s : ℝ) : ℝ := max 0 (min 1 s)

private def clampRectangle (p : LoopPlane) : LoopPlane :=
  annulusPoint (clampAngular (p 0)) (clampRadial (p 1))

private theorem clampAngular_mem (x : ℝ) : clampAngular x ∈ Icc 0 curvePeriod := by
  have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  exact ⟨le_max_left _ _, max_le hP (min_le_left _ _)⟩

private theorem clampRadial_mem (s : ℝ) : clampRadial s ∈ Icc 0 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

private theorem clampRectangle_mem (p : LoopPlane) : clampRectangle p ∈ m64AnnulusDomain := by
  exact ⟨(clampAngular_mem (p 0)).1, (clampAngular_mem (p 0)).2,
    (clampRadial_mem (p 1)).1, (clampRadial_mem (p 1)).2⟩

private theorem clampRectangle_eq {p : LoopPlane} (hp : p ∈ m64AnnulusDomain) :
    clampRectangle p = p := by
  change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 at hp
  ext i
  fin_cases i
  · simp [clampRectangle, annulusPoint, clampAngular, min_eq_right hp.2.1,
      max_eq_right hp.1]
  · simp [clampRectangle, annulusPoint, clampRadial, min_eq_right hp.2.2.2,
      max_eq_right hp.2.2.1]

theorem closed_rectangle_exists_circle_phase {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (hf : ContinuousOn f m64AnnulusDomain)
    (hf1 : ContMDiffOn (𝓡 2) (𝓡 1) 1 f (interior m64AnnulusDomain))
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      C.quotient (L0 x) = f (annulusPoint x 0)) :
    ∃ L : LoopPlane → ℝ, Continuous L ∧
      ContDiffOn ℝ 1 L (interior m64AnnulusDomain) ∧
      (∀ p ∈ m64AnnulusDomain, C.quotient (L p) = f p) ∧
      ∀ x ∈ Icc (0 : ℝ) curvePeriod, L (annulusPoint x 0) = L0 x := by
  let := C.chartedSpace
  have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have hclamp : Continuous clampRectangle := by
    unfold clampRectangle clampAngular clampRadial annulusPoint
    fun_prop
  have hF : Continuous (f ∘ clampRectangle) :=
    hf.comp_continuous hclamp clampRectangle_mem
  have hbase : C.quotient (L0 0) = (f ∘ clampRectangle) (annulusPoint 0 0) := by
    rw [Function.comp_apply, clampRectangle_eq (show annulusPoint 0 0 ∈ m64AnnulusDomain from
      ⟨le_rfl, hP, le_rfl, zero_le_one⟩)]
    exact hzero 0 ⟨le_rfl, hP⟩
  let cov := AddCircle.isCoveringMap_coe circumference
  obtain ⟨L, hL, -⟩ := cov.existsUnique_continuousMap_lifts
    ⟨f ∘ clampRectangle, hF⟩ (annulusPoint 0 0) (L0 0) hbase
  have hquot (p : LoopPlane) : C.quotient (L p) = f (clampRectangle p) := congrFun hL.2 p
  have hquotS (p : LoopPlane) (hp : p ∈ m64AnnulusDomain) : C.quotient (L p) = f p := by
    rw [hquot, clampRectangle_eq hp]
  have hregular : ContDiffOn ℝ 1 L (interior m64AnnulusDomain) := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply contMDiffAt_iff_contDiffAt.mp
    apply (C.quotient_local_diffeomorph (L p)).contMDiffAt_of_comp
      (I := 𝓡 2) (m := 1) (by decide) L.continuous.continuousAt
    have hnear : C.quotient ∘ L =ᶠ[𝓝 p] f := by
      filter_upwards [isOpen_interior.mem_nhds hp] with q hq
      exact hquotS q (interior_subset hq)
    exact ((hf1 p hp).contMDiffAt (isOpen_interior.mem_nhds hp)).congr_of_eventuallyEq hnear
  have hline : Continuous (fun x : ℝ => annulusPoint x 0) := by
    unfold annulusPoint
    fun_prop
  have hangular : Continuous clampAngular := by unfold clampAngular; fun_prop
  have hlower : ∀ x, L (annulusPoint x 0) = L0 (clampAngular x) := by
    have heq := cov.eq_of_comp_eq (L.continuous.comp hline) (hL0.comp hangular)
      (show (fun x => (L (annulusPoint x 0) : AddCircle circumference)) =
        (fun x => (L0 (clampAngular x) : AddCircle circumference)) from by
          funext x
          change C.quotient (L (annulusPoint x 0)) = C.quotient (L0 (clampAngular x))
          rw [hquot]
          simpa only [clampRectangle, annulusPoint, Matrix.cons_val_zero,
            Matrix.cons_val_one, clampRadial, min_eq_right zero_le_one, max_self] using
              (hzero (clampAngular x) (clampAngular_mem x)).symm)
      0 (by simpa [clampAngular, min_eq_right hP] using hL.1)
    exact congrFun heq
  refine ⟨L, L.continuous, hregular, hquotS, ?_⟩
  intro x hx
  rw [hlower]
  simp only [clampAngular, min_eq_right hx.2, max_eq_right hx.1]

theorem closed_rectangle_phase_boundary_difference {circumference : ℝ}
    (C : M62.CircleGeometry circumference) (f : LoopPlane → C.Point)
    (L : LoopPlane → ℝ) (hL : Continuous L)
    (hquot : ∀ p ∈ m64AnnulusDomain, C.quotient (L p) = f p)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (Lb : ℝ → ℝ) (hLb : Continuous Lb)
    (hb : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      C.quotient (Lb x) = f (annulusPoint x s)) :
    ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      L (annulusPoint x s) = Lb x + (L (annulusPoint 0 s) - Lb 0) := by
  have hP : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  let d := L (annulusPoint 0 s) - Lb 0
  have hd : (d : AddCircle circumference) = 0 := by
    change ((L (annulusPoint 0 s) - Lb 0 : ℝ) : AddCircle circumference) = 0
    rw [AddCircle.coe_sub]
    apply sub_eq_zero.mpr
    exact (hquot _ ⟨le_rfl, hP, hs.1, hs.2⟩).trans (hb 0 ⟨le_rfl, hP⟩).symm
  have hangular : Continuous clampAngular := by unfold clampAngular; fun_prop
  have hline : Continuous (fun x : ℝ => annulusPoint (clampAngular x) s) := by
    unfold annulusPoint
    fun_prop
  have heq := (AddCircle.isCoveringMap_coe circumference).eq_of_comp_eq
    (hL.comp hline) ((hLb.comp hangular).add continuous_const)
    (show (fun x => (L (annulusPoint (clampAngular x) s) : AddCircle circumference)) =
      (fun x => ((Lb (clampAngular x) + d : ℝ) : AddCircle circumference)) from by
        funext x
        rw [AddCircle.coe_add, hd, add_zero]
        exact (hquot _ ⟨(clampAngular_mem x).1, (clampAngular_mem x).2, hs.1, hs.2⟩).trans
          (hb (clampAngular x) (clampAngular_mem x)).symm)
    0 (by simp only [Function.comp_apply, Pi.add_apply, clampAngular,
      min_eq_right hP, max_self]; ring)
  intro x hx
  have h := congrFun heq x
  simpa only [Function.comp_apply, Pi.add_apply, clampAngular,
    min_eq_right hx.2, max_eq_right hx.1] using h

end PoincareConjecture.M64
