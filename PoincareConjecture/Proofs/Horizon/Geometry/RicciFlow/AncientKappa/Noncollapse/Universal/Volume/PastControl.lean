import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Volume.Preparations
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem operator_bound_of_tensor_calculus (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0)
    (hcalculus : (K.flow.connection t).CurvatureTensorCalculus) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      (K.flow.connection t).CurvatureOperatorBound C x := by
  obtain ⟨C, hC, hbound⟩ := K.bounded_curvature t ht
  refine ⟨(n : ℝ) ^ 2 * C, by positivity, ?_⟩
  intro x U hU
  have hop := ((K.flow.connection t).curvatureOperatorBound_scalarCurvature
    hcalculus x (K.nonnegative_curvature_operator t ht x)).2 U hU
  apply hop.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact (le_abs_self _).trans
    (((K.flow.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (sq_nonneg _)))

theorem scalar_monotone_of_differential (K : AncientKappaSolution n M)
    (hdifferential : ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x) dR
          (Iic 0) t ∧
        dR + 2 * (mvfderiv (𝓡 n)
          (fun y => (K.flow.connection t).scalarCurvature y) x) v +
          2 * (K.flow.connection t).ricci x v v ≥ 0)
    (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 0) (x : M) :
    (K.flow.connection s).scalarCurvature x ≤
      (K.flow.connection t).scalarCurvature x := by
  classical
  have hderiv (a : ℝ) (ha : a ≤ 0) :
      ∃ dR : ℝ,
        HasDerivWithinAt (fun b => (K.flow.connection b).scalarCurvature x) dR
          (Iic 0) a ∧ 0 ≤ dR := by
    obtain ⟨dR, hdR, hi⟩ := hdifferential a ha x 0
    refine ⟨dR, hdR, ?_⟩
    have hz : (K.flow.connection a).ricci x 0 0 = 0 := by
      rw [(K.flow.connection a).ricci_eq_sum_frame x 0 0]
      simp
    simpa only [hz, map_zero, mul_zero, add_zero] using hi
  have hm : MonotoneOn (fun a => (K.flow.connection a).scalarCurvature x) (Iic 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0)
      (fun a ha => (hderiv a ha).choose_spec.1.continuousWithinAt)
      (f' := fun a => if ha : a ≤ 0 then (hderiv a ha).choose else 0)
    · intro a ha
      have ha' : a ∈ Iic (0 : ℝ) := interior_subset ha
      simpa only [dif_pos (show a ≤ 0 from ha')] using
        (hderiv a ha').choose_spec.1.mono
          (show interior (Iic (0 : ℝ)) ⊆ Iic 0 from interior_subset)
    · intro a ha
      have ha' : a ∈ Iic (0 : ℝ) := interior_subset ha
      simpa only [dif_pos (show a ≤ 0 from ha')] using (hderiv a ha').choose_spec.2
  exact hm (hst.trans ht) ht hst

theorem exists_scalar_pos_of_tensor_calculus (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0)
    (hcalculus : (K.flow.connection t).CurvatureTensorCalculus) :
    ∃ x : M, 0 < (K.flow.connection t).scalarCurvature x := by
  obtain ⟨x, hx⟩ := K.nonflat t ht
  refine ⟨x, ?_⟩
  have hpos : 0 < (K.flow.connection t).curvatureTensorNorm x :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) hx.symm
  exact hpos.trans_le
    ((K.flow.connection t).curvatureTensorNorm_le_scalarCurvature_sharp hcalculus x
      (K.nonnegative_curvature_operator t ht x))

theorem whole_past_bound_of_scalar_monotone (K : AncientKappaSolution n M)
    (hcalculus : ∀ t ≤ 0, (K.flow.connection t).CurvatureTensorCalculus)
    (hmonotone : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
      (K.flow.connection s).scalarCurvature x ≤
        (K.flow.connection t).scalarCurvature x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≤ 0, ∀ x : M,
      (K.flow.connection t).curvatureTensorNorm x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := K.bounded_curvature 0 le_rfl
  refine ⟨(n : ℝ) * C, by positivity, ?_⟩
  intro t ht x
  calc
    _ ≤ (K.flow.connection t).scalarCurvature x :=
      (K.flow.connection t).curvatureTensorNorm_le_scalarCurvature_sharp
        (hcalculus t ht) x (K.nonnegative_curvature_operator t ht x)
    _ ≤ (K.flow.connection 0).scalarCurvature x := hmonotone t 0 ht le_rfl x
    _ ≤ (n : ℝ) * (K.flow.connection 0).curvatureTensorNorm x :=
      (K.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp x
    _ ≤ (n : ℝ) * C :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (Nat.cast_nonneg n)

end PoincareConjecture.AncientKappaSolution
