import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderCharts
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndCompactSlabs
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)



def endCylinderChartRegion : Set E₃ :=
  Metric.ball 0 6 ∩ {x : E₃ | x 2 ∈ Ioo (3 : ℝ) 5}



theorem endCylinderChartRegion_isOpen : IsOpen endCylinderChartRegion :=
  Metric.isOpen_ball.inter
    (isOpen_Ioo.preimage (EuclideanSpace.proj 2 : E₃ →L[ℝ] ℝ).continuous)

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

private theorem endStereographicChart_sequence_jet_bounds (q : ℕ → UnitTwoSphere) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ i x, x ∈ endCylinderChartRegion →
      ‖iteratedFDeriv ℝ m (endStereographicChart e (q i)) x‖ ≤ C := by
  let A : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := stereographicCylinderCoefficients 2
  let B : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ := g.euclideanCoefficients
  have hA : ContDiff ℝ ∞ A :=
    stereographicCylinderCoefficients_contDiff.comp (contDiff_const.prodMk contDiff_id)
  have hB : ContDiff ℝ ∞ B := contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hslab := endClosedSlab_isCompact e (a := 3) (b := 5) (by norm_num)
  obtain ⟨R, hR⟩ := hslab.isBounded.exists_norm_le
  let V : Set E₃ := Metric.ball 0 (R + 1)
  have hmap : ∀ i, MapsTo (endStereographicChart e (q i)) endCylinderChartRegion V := by
    intro i x hx
    have hs : endStereographicChart e (q i) x ∈ endClosedSlab e 3 5 :=
      ⟨sphereCylinderChart (q i) x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩, rfl⟩
    simpa only [V, Metric.mem_ball, dist_zero_right] using
      (hR _ hs).trans_lt (lt_add_one R)
  obtain ⟨aA, haA, hAlow⟩ := exists_uniform_bilinear_lower_bound
    (isCompact_closedBall (0 : E₃) 6) hA.continuous.continuousOn
    (fun x _ v hv => stereographicCylinderCoefficients_pos (by norm_num) x v hv)
  obtain ⟨aB, haB, hBlow⟩ := exists_uniform_bilinear_lower_bound
    (isCompact_closedBall (0 : E₃) (R + 1)) hB.continuous.continuousOn
    (fun x _ v hv => g.pos x v hv)
  have hpos : 0 < min aA aB := lt_min haA haB
  have hf : ∀ i, ContDiffOn ℝ ∞ (endStereographicChart e (q i)) endCylinderChartRegion := by
    intro i x hx
    have hs : ContDiffAt ℝ ∞ (endStereographicChart e (q i)) x :=
      contMDiffAt_iff_contDiffAt.mp
        (endStereographicChart_contMDiffAt e (q i) (by have := hx.2.1; linarith))
    exact hs.contDiffWithinAt
  apply CoordinateTransition.uniform_derivative_bounds_of_local_isometries
    (A := fun _ => A) (B := fun _ => B)
    (f := fun i => endStereographicChart e (q i))
    endCylinderChartRegion_isOpen Metric.isOpen_ball Metric.isBounded_ball
    (fun _ => hA.contDiffOn) (fun _ => hB.contDiffOn) hf
    (fun _ x _ u v => by
      simp only [A, stereographicCylinderCoefficients_apply]
      ring)
    (fun _ x _ u v => g.symm x u v) hpos
    (fun _ x hx v => (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
      (hAlow x (Metric.ball_subset_closedBall hx.1) v))
    (fun _ x hx v => (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
      (hBlow x (Metric.ball_subset_closedBall hx) v))
    ?_ hmap ?_
  · intro m
    obtain ⟨CA, hCA⟩ := (isCompact_closedBall (0 : E₃) 6).exists_bound_of_continuousOn
      ((hA.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn)
    obtain ⟨CB, hCB⟩ := (isCompact_closedBall (0 : E₃) (R + 1)).exists_bound_of_continuousOn
      ((hB.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)).continuousOn)
    exact ⟨max CA CB,
      fun _ x hx => (hCA x (Metric.ball_subset_closedBall hx.1)).trans (le_max_left _ _),
      fun _ x hx => (hCB x (Metric.ball_subset_closedBall hx)).trans (le_max_right _ _)⟩
  · intro i x hx u v
    have h := endCylinderAuxMetric_stereographic e (q i) 0
      (by have := hx.2.1; linarith : 2 < x 2) u v
    rw [endCylinderAuxMetric_zero, mfderiv_eq_fderiv] at h
    norm_num [endCylinderParameter] at h
    convert! h using 1



theorem endStereographicChart_uniform_jet_bounds (m : ℕ) :
    ∃ C : ℝ, ∀ (q : UnitTwoSphere) x, x ∈ endCylinderChartRegion →
      ‖iteratedFDeriv ℝ m (endStereographicChart e q) x‖ ≤ C := by
  classical
  by_contra! h
  choose q x hx hlarge using fun n : ℕ => h (n : ℝ)
  obtain ⟨C, hC⟩ := endStereographicChart_sequence_jet_bounds e q m
  obtain ⟨n, hn⟩ := exists_nat_gt C
  exact (not_lt_of_ge (hC n (x n) (hx n))) (hn.trans (hlarge n))

end PoincareConjecture.M34
