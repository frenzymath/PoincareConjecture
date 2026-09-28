import PoincareConjecture.Proofs.M14.Sec6_6_RescalingInitialValue
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialFamily
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialCoherence

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hCoordinates : M12MetricPredecessors.{0} n)
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

noncomputable def rescalingExponentialFamily (hM04 : RicciFlowCurvatureTheory.{0})
    {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x) :
    M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x :=
  exponentialFamily hM04 hM12 (by
    change parabolicTime Q a (G.spacetime.timeFunction x) = parabolicTime Q a T
    rw [E.base_time])

include hCoordinates in

theorem rescalingExponential_domain_iff {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) (s : ℝ) :
    (Z, s) ∈ E.domain ↔
      (rescalingInitialEquiv G.spacetime Q hQ a x Z, Real.sqrt Q * s) ∈ E'.domain := by
  have hroot := Real.sqrt_pos.mpr hQ
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · constructor
    · intro hs
      have hnonneg := (E.domain_admissible hs).1
      exact False.elim (not_le.mpr hneg hnonneg)
    · intro hs
      have hnonneg := (E'.domain_admissible hs).1
      exact False.elim (not_le.mpr (mul_neg_of_pos_of_neg hroot hneg) hnonneg)
  · subst s
    simp only [mul_zero]
    exact iff_of_true (E.domain_zero Z) (E'.domain_zero _)
  · have hpos' := mul_pos hroot hpos
    have hsq : (Real.sqrt Q * s) ^ 2 = Q * s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
    constructor
    · intro hs
      obtain ⟨y, ⟨P⟩⟩ := (E.positive_survival_iff Z s hpos).mp hs
      apply (E'.positive_survival_iff _ _ hpos').mpr
      refine ⟨y, ?_⟩
      rw [hsq]
      exact rescalingInitialValuePath hCoordinates hM12 hM13 G Q hQ a P
    · intro hs
      obtain ⟨y, hP⟩ := (E'.positive_survival_iff _ _ hpos').mp hs
      rw [hsq] at hP
      obtain ⟨P⟩ := hP
      exact (E.positive_survival_iff Z s hpos).mpr
        ⟨y, rescalingInitialValuePath_inverse hCoordinates hM12 hM13 G Q hQ a P⟩

include hCoordinates in

theorem rescalingExponential_gamma {T : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x) (s : ℝ) (hs : (Z, s) ∈ E.domain) :
    E'.gamma (rescalingInitialEquiv G.spacetime Q hQ a x Z) (Real.sqrt Q * s) =
      E.gamma Z s := by
  rcases eq_or_lt_of_le (E.domain_admissible hs).1 with hzero | hpos
  · change 0 = s at hzero
    subst s
    rw [mul_zero, E'.gamma_at_zero, E.gamma_at_zero]
  · have hpos' := mul_pos (Real.sqrt_pos.mpr hQ) hpos
    have hsq : (Real.sqrt Q * s) ^ 2 = Q * s ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
    have ht : Nonempty (M14SquareRootInitialValuePath (rescalingTransport hM12 hM13 G Q hQ a)
        (parabolicTime Q a T) ((Real.sqrt Q * s) ^ 2) x (E.gamma Z s)
        (rescalingInitialEquiv G.spacetime Q hQ a x Z)) := by
      rw [hsq]
      exact rescalingInitialValuePath hCoordinates hM12 hM13 G Q hQ a
        (exponentialInitialValuePath E Z s hs hpos)
    obtain ⟨P⟩ := ht
    have heq := E'.initial_value_agreement
      (rescalingInitialEquiv G.spacetime Q hQ a x Z) (Real.sqrt Q * s) hpos' (E.gamma Z s) P
      ⟨(sq_pos_of_pos hpos').le, le_rfl⟩
    rw [P.path.curve_end] at heq
    dsimp only at heq
    erw [Real.sqrt_sq hpos'.le] at heq
    exact heq.symm

include hCoordinates in

theorem rescalingExponential_originalTime {T τ : ℝ} {x : G.Point}
    (E : M14ExponentialFamily G T x)
    (E' : M14ExponentialFamily (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) x) (Z : G.Horizontal x)
    (hs : (Z, Real.sqrt τ) ∈ E.domain) {r : ℝ} (hr : r ∈ Icc 0 τ) :
    E'.gamma (rescalingInitialEquiv G.spacetime Q hQ a x Z) (Real.sqrt (Q * r)) =
      E.gamma Z (Real.sqrt r) := by
  have hsurv := (E.maximal_lifetime Z).out (E.domain_zero Z) hs
    ⟨Real.sqrt_nonneg r, Real.sqrt_le_sqrt hr.2⟩
  simpa only [Real.sqrt_mul hQ.le] using
    rescalingExponential_gamma hCoordinates hM12 hM13 G Q hQ a E E' Z (Real.sqrt r) hsurv

end PoincareConjecture.M14
