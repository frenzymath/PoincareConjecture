import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem low_scalar_point_of_action {T S Q : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 S x y) (hQ : 0 ≤ Q)
    (hmargin : 3 < (Q / 16 - 6) * S)
    (hscalar : ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature G.leafwise (p.curve s))
    (haction : M14BackwardLAction G p ≤ 3 * Real.sqrt S) :
    ∃ s ∈ Icc (3 * S / 4) (7 * S / 8),
      horizontalScalarCurvature G.leafwise (p.curve s) < Q := by
  by_contra! hhigh
  have hS : 0 < S := p.tau_lt
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hleft : 0 ≤ 3 * S / 4 := by positivity
  have hright : 7 * S / 8 ≤ S := by linarith
  have hmid : 3 * S / 4 ≤ 7 * S / 8 := by linarith
  let f : ℝ → ℝ := fun s => M14BackwardLIntegrand G p s + 6 * Real.sqrt S
  have hf : IntervalIntegrable f volume 0 S :=
    p.action_integrable.add intervalIntegrable_const
  have henergy (s : ℝ) : 0 ≤ G.spacetime.horizontalMetric.inner (p.curve s)
      (p.horizontal_velocity s) (p.horizontal_velocity s) :=
    (G.spacetime.horizontalMetric.toRiemannianMetric.toCore
      (p.curve s)).re_inner_nonneg _
  have hnonneg (s : ℝ) (hs : s ∈ Icc 0 S) : 0 ≤ f s := by
    have hsum : -6 ≤ horizontalScalarCurvature G.leafwise (p.curve s) +
        G.spacetime.horizontalMetric.inner (p.curve s)
          (p.horizontal_velocity s) (p.horizontal_velocity s) := by
      linarith [hscalar s hs, henergy s]
    have hmul := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg s)
    have hsqrtle : Real.sqrt s ≤ Real.sqrt S := Real.sqrt_le_sqrt hs.2
    dsimp [f, M14BackwardLIntegrand, M14RawLIntegrand]
    nlinarith
  have hfmid : IntervalIntegrable f volume (3 * S / 4) (7 * S / 8) := by
    apply hf.mono_set
    rw [uIcc_of_le hmid, uIcc_of_le hS.le]
    exact Icc_subset_Icc hleft hright
  have hpoint (s : ℝ) (hs : s ∈ Icc (3 * S / 4) (7 * S / 8)) :
      Q * Real.sqrt S / 2 ≤ f s := by
    have hroot : Real.sqrt S / 2 ≤ Real.sqrt s := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt hS.le, hs.1]
    have hsum : Q ≤ horizontalScalarCurvature G.leafwise (p.curve s) +
        G.spacetime.horizontalMetric.inner (p.curve s)
          (p.horizontal_velocity s) (p.horizontal_velocity s) := by
      linarith [hhigh s hs, henergy s]
    have hmul := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg s)
    have hmulroot := mul_le_mul_of_nonneg_left hroot hQ
    dsimp [f, M14BackwardLIntegrand, M14RawLIntegrand]
    nlinarith [Real.sqrt_nonneg S]
  have hlower := intervalIntegral.integral_mono_on hmid
    (intervalIntegrable_const (c := Q * Real.sqrt S / 2)) hfmid hpoint
  have hupper := intervalIntegral.integral_mono_interval hleft hmid hright
    ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all volume (fun s hs => hnonneg s ⟨hs.1.le, hs.2⟩))) hf
  have hvalue : (∫ s in (0 : ℝ)..S, f s) =
      M14BackwardLAction G p + S * (6 * Real.sqrt S) := by
    change (∫ s in (0 : ℝ)..S,
      M14RawLIntegrand G p.curve p.horizontal_velocity s + 6 * Real.sqrt S) = _
    rw [intervalIntegral.integral_add p.action_integrable intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, M14BackwardLAction, M14BackwardLIntegrand]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlower
  rw [hvalue] at hupper
  have hscaled := mul_lt_mul_of_pos_right hmargin hsqrt
  nlinarith

theorem prefix_low_scalar_action_margin {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {S : ℝ} (hS : 1 / 32 ≤ S) :
    3 < ((p.r (Fin.last p.i))⁻¹ ^ 2 / 16 - 6) * S := by
  have hr : p.r (Fin.last p.i) ≤ 1 / 200 :=
    (p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))
  have hinv : (200 : ℝ) ≤ (p.r (Fin.last p.i))⁻¹ := by
    have h := one_div_le_one_div_of_le (p.r_pos (Fin.last p.i)) hr
    norm_num at h
    exact h
  have hQ : (40000 : ℝ) ≤ (p.r (Fin.last p.i))⁻¹ ^ 2 := by nlinarith
  have hcoeff : (2494 : ℝ) ≤ (p.r (Fin.last p.i))⁻¹ ^ 2 / 16 - 6 := by
    linarith
  have hprod := mul_le_mul hcoeff hS (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (by linarith : 0 ≤ (p.r (Fin.last p.i))⁻¹ ^ 2 / 16 - 6)
  exact (by norm_num : (3 : ℝ) < 2494 * (1 / 32)).trans_le hprod

theorem middle_interval_subset_old_window {a T epsilon : ℝ}
    (ha : 1 / 32 ≤ a) (hTlo : 2 * a ≤ T) (hThi : T ≤ 4 * a)
    (hepsilon : 0 ≤ epsilon) (hepsle : epsilon ≤ 1 / 200) :
    Icc (3 * (T - a) / 4) (7 * (T - a) / 8) ⊆
      Icc (max (epsilon ^ 2) (T - 2 * a)) (T - a - epsilon ^ 2) := by
  have hepssq : epsilon ^ 2 ≤ (1 / 40000 : ℝ) := by nlinarith
  intro s hs
  refine ⟨max_le_iff.mpr ⟨?_, ?_⟩, ?_⟩ <;> nlinarith [hs.1, hs.2]

end PoincareConjecture.Proofs.M46
