import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MetricInteriorFan













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture





theorem m64Intrinsic_linear_kernel_null
    (ell : AnnulusCoordinates →L[ℝ] ℝ) (hell : ell ≠ 0) :
    volume {w : AnnulusCoordinates | ell w = 0} = 0 := by
  change volume (LinearMap.ker ell.toLinearMap : Set AnnulusCoordinates) = 0
  apply Measure.addHaar_submodule
  rw [Ne, LinearMap.ker_eq_top]
  intro hzero
  apply hell
  ext w
  exact congrArg (fun L : AnnulusCoordinates →ₗ[ℝ] ℝ => L w) hzero






theorem m64Intrinsic_metric_halfplane_fan_angle_sum
    {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates)
    (ell : AnnulusCoordinates →L[ℝ] ℝ) (hell : ell ≠ 0)
    (x y : I → AnnulusCoordinates) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, g.cornerAngle q (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hside : ∀ (i : I) (a c : ℝ), 0 < a → 0 < c → 0 < ell (a • x i + c • y i))
    (hpartition : ∀ᵐ w : AnnulusCoordinates, 0 < ell w →
      ∃! i, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i) :
    (∑ i, g.cornerAngle q (x i) (y i)) = Real.pi := by
  let C (i : I) (w : AnnulusCoordinates) :=
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i
  let X : I ⊕ I → AnnulusCoordinates := Sum.elim x (fun i => -x i)
  let Y : I ⊕ I → AnnulusCoordinates := Sum.elim y (fun i => -y i)
  let D (i : I ⊕ I) (w : AnnulusCoordinates) :=
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • X i + c • Y i
  have hpositive {i : I} {w : AnnulusCoordinates} (hw : C i w) : 0 < ell w := by
    obtain ⟨a, c, ha, hc, rfl⟩ := hw
    exact hside i a c ha hc
  have hneg (i : I) (w : AnnulusCoordinates) : D (Sum.inr i) w ↔ C i (-w) := by
    constructor
    · rintro ⟨a, c, ha, hc, hw⟩
      refine ⟨a, c, ha, hc, ?_⟩
      simpa only [X, Y, Sum.elim_inr, smul_neg, neg_add_rev, neg_neg, add_comm]
        using congrArg Neg.neg hw
    · rintro ⟨a, c, ha, hc, hw⟩
      refine ⟨a, c, ha, hc, ?_⟩
      simpa only [X, Y, Sum.elim_inr, smul_neg, neg_add_rev, neg_neg, add_comm]
        using congrArg Neg.neg hw
  have hline : ∀ᵐ w : AnnulusCoordinates, ell w ≠ 0 := by
    simpa only [ae_iff, not_not] using m64Intrinsic_linear_kernel_null ell hell
  have hpartition_neg := (Measure.measurePreserving_neg
    (volume : Measure AnnulusCoordinates)).quasiMeasurePreserving.ae hpartition
  have hfull : ∀ᵐ w : AnnulusCoordinates, ∃! i, D i w := by
    filter_upwards [hline, hpartition, hpartition_neg] with w hw hp hn
    rcases lt_or_gt_of_ne hw with hnegative | hpositive'
    · have hminus : 0 < ell (-w) := by simpa only [map_neg] using neg_pos.mpr hnegative
      obtain ⟨i, hi, huniq⟩ := hn hminus
      refine ⟨Sum.inr i, (hneg i w).mpr hi, ?_⟩
      intro j hj
      cases j with
      | inl j =>
        have hpos := hpositive hj
        exact False.elim (not_lt_of_ge hnegative.le hpos)
      | inr j => exact congrArg Sum.inr (huniq j ((hneg j w).mp hj))
    · obtain ⟨i, hi, huniq⟩ := hp hpositive'
      refine ⟨Sum.inl i, hi, ?_⟩
      intro j hj
      cases j with
      | inl j => exact congrArg Sum.inl (huniq j hj)
      | inr j =>
        have hpos := hpositive ((hneg j w).mp hj)
        rw [map_neg] at hpos
        linarith
  have hsum := m64Intrinsic_metric_fan_angle_sum g q X Y
    (fun i => by cases i with
      | inl i => exact hx i
      | inr i => exact neg_ne_zero.mpr (hx i))
    (fun i => by cases i with
      | inl i => exact hy i
      | inr i => exact neg_ne_zero.mpr (hy i))
    (fun i => by cases i with
      | inl i => exact hangle i
      | inr i => simpa only [X, Y, Sum.elim_inr, g.cornerAngle_neg_neg] using hangle i)
    hfull
  simp only [Fintype.sum_sum_type, X, Y, Sum.elim_inl, Sum.elim_inr,
    g.cornerAngle_neg_neg] at hsum
  linarith

end PoincareConjecture
