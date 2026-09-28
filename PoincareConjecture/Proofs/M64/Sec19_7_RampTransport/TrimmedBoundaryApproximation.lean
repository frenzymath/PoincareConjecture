import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.StripCurveConvergence

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

structure TrimmedBoundaryControl (F : RicciFlow n M (Icc a b)) (time : ℝ)
    (f : LoopPlane → M) (r epsilon width : ℝ) : Prop where
  width_pos : 0 < width
  width_lt_half : width < 1 / 2
  lower_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => f (annulusPoint x width))
  upper_smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => f (annulusPoint x (1 - width)))
  lower_periodic : Function.Periodic (fun x => f (annulusPoint x width)) curvePeriod
  upper_periodic : Function.Periodic (fun x => f (annulusPoint x (1 - width))) curvePeriod
  lower_immersed : ∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y width)) x ≠ 0
  upper_immersed : ∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y (1 - width))) x ≠ 0
  lower_length_error : |m62Length F (fun y _ => f (annulusPoint y width)) time -
    m62Length F (fun y _ => f (annulusPoint y 0)) time| < epsilon
  upper_length_error : |m62Length F (fun y _ => f (annulusPoint y (1 - width))) time -
    m62Length F (fun y _ => f (annulusPoint y 1)) time| < epsilon
  lower_length_strict : r / 4 < m62Length F (fun y _ => f (annulusPoint y width)) time
  lower_turning : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
    m63ArcLength F (fun y _ => f (annulusPoint y width)) time alpha beta ≤ r / 4 →
    m63ArcTotalCurvature F (fun y _ => f (annulusPoint y width)) time alpha beta < (7 / 800 : ℝ)

theorem exists_trimmed_boundary_tolerance [T2Space M] [CompactSpace M]
    (F : RicciFlow n M (Icc a b)) {time : ℝ} (htime : time ∈ Icc a b)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 2 f S)
    (hi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ f m64AnnulusOpenStrip)
    (hp : ∀ s ∈ Icc (0 : ℝ) 1,
      Function.Periodic (fun x => f (annulusPoint x s)) curvePeriod)
    (himm0 : ∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y 0)) x ≠ 0)
    (himm1 : ∀ x, curveVelocity (n := n) (fun y => f (annulusPoint y 1)) x ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (hlength : r / 2 < m62Length F (fun y _ => f (annulusPoint y 0)) time)
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength F (fun y _ => f (annulusPoint y 0)) time alpha beta ≤ r / 2 →
      m63ArcTotalCurvature F (fun y _ => f (annulusPoint y 0)) time alpha beta < (3 / 400 : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 4 ∧
      ∀ width : ℝ, 0 < width → width < delta →
        TrimmedBoundaryControl F time f r epsilon width := by
  let : Nonempty M := ⟨f (annulusPoint 0 0)⟩
  obtain ⟨dimension, e, he, hemb, hinj⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, rho, hU, heU, hrho, hre, _hmin, _huniq⟩ :=
    M63.exists_smooth_compact_embedded_retraction e hemb he hinj
  let tolerance := min epsilon (min (r / 8) (1 / 800))
  have htolerance : 0 < tolerance := lt_min hepsilon (lt_min (by positivity) (by norm_num))
  have htolr : tolerance ≤ r / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have htold : tolerance ≤ (1 / 800 : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨delta0, hdelta0, hnear0⟩ := exists_annulus_slice_subarc_tolerance_of_retraction
    F he hU heU hrho hre htime hf hp (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      himm0 htolerance
  obtain ⟨delta1, hdelta1, hnear1⟩ := exists_annulus_slice_subarc_tolerance_of_retraction
    F he hU heU hrho hre htime hf hp (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      himm1 hepsilon
  let delta := min (1 / 4) (min delta0 delta1)
  refine ⟨delta, lt_min (by norm_num) (lt_min hdelta0 hdelta1), min_le_left _ _, ?_⟩
  intro width hwidth hsmall
  have hhalf : width < 1 / 2 := hsmall.trans_le ((min_le_left _ _).trans (by norm_num))
  have hlow : width ∈ Ioo (0 : ℝ) 1 := ⟨hwidth, by linarith⟩
  have hupp : 1 - width ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hd0 : |width - 0| < delta0 := by
    simpa only [sub_zero, abs_of_pos hwidth] using
      hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd1 : |(1 - width) - 1| < delta1 := by
    rw [show (1 - width) - 1 = -width by ring, abs_neg, abs_of_pos hwidth]
    exact hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hlowImm, harcs0⟩ := hnear0 width (Ioo_subset_Icc_self hlow) hd0
  obtain ⟨huppImm, harcs1⟩ := hnear1 (1 - width) (Ioo_subset_Icc_self hupp) hd1
  have hperiod : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hlen0 := (harcs0 0 curvePeriod hperiod (by simp)).1
  have hlen1 := (harcs1 0 curvePeriod hperiod (by simp)).1
  refine {
    width_pos := hwidth
    width_lt_half := hhalf
    lower_smooth := annulus_slice_contMDiff le_rfl hi hlow
    upper_smooth := annulus_slice_contMDiff le_rfl hi hupp
    lower_periodic := hp width (Ioo_subset_Icc_self hlow)
    upper_periodic := hp (1 - width) (Ioo_subset_Icc_self hupp)
    lower_immersed := hlowImm
    upper_immersed := huppImm
    lower_length_error := hlen0.trans_le (min_le_left _ _)
    upper_length_error := hlen1
    lower_length_strict := ?_
    lower_turning := ?_ }
  · have herror := (abs_lt.mp (hlen0.trans_le htolr)).1
    change -(r / 8) < m62Length F (fun y _ => f (annulusPoint y width)) time -
      m62Length F (fun y _ => f (annulusPoint y 0)) time at herror
    linarith
  · intro alpha beta hab hper hshort
    have herrors := harcs0 alpha beta hab hper
    have hlengthError := (abs_lt.mp (herrors.1.trans_le htolr)).1
    have hsource := hturn alpha beta hab hper (by linarith)
    have hturnError := (abs_lt.mp (herrors.2.trans_le htold)).2
    linarith

end PoincareConjecture.M64.RampTransport
