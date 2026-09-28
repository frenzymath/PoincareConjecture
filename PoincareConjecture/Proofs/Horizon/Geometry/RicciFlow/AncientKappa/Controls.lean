import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem operator_bound (hM04 : RicciFlowCurvatureTheory.{u})
    (K : AncientKappaSolution n M) (t : ℝ) (ht : t ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      (K.flow.connection t).CurvatureOperatorBound C x := by
  obtain ⟨C, hC, hbound⟩ := K.bounded_curvature t ht
  refine ⟨(n : ℝ) ^ 2 * C, by positivity, ?_⟩
  intro x U hU
  have hop := ((K.flow.connection t).curvatureOperatorBound_scalarCurvature
    (hM04.tensor_calculus n M _ _) x (K.nonnegative_curvature_operator t ht x)).2 U hU
  apply hop.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact (le_abs_self _).trans (((K.flow.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hbound x)) (sq_nonneg _)))

theorem scalar_pos (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u}) (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0) (x : M) :
    0 < (K.flow.connection t).scalarCurvature x := by
  have ht' : t - 1 ≤ 0 := by linarith
  obtain ⟨p, hp⟩ := K.nonflat (t - 1) ht'
  have hnorm : 0 ≤ (K.flow.connection (t - 1)).curvatureTensorNorm p := Real.sqrt_nonneg _
  have hnormpos : 0 < (K.flow.connection (t - 1)).curvatureTensorNorm p :=
    lt_of_le_of_ne hnorm hp.symm
  have hscalar : 0 < (K.flow.connection (t - 1)).scalarCurvature p := by
    have hb := (K.flow.connection (t - 1)).curvatureTensorNorm_le_scalarCurvature
      (hM04.tensor_calculus n M _ _) p (K.nonnegative_curvature_operator _ ht' p)
    exact (mul_pos_iff.mp (hnormpos.trans_le hb)).resolve_right
      (fun h => (not_lt_of_ge (sq_nonneg (n : ℝ))) h.1) |>.2
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(K.flow.metric t).toRiemannianMetric⟩
  have hfinite : Manifold.riemannianEDist (𝓡 n) p x < ⊤ :=
    lt_top_iff_ne_top.mpr ((K.flow.metric t).edist_ne_top p x)
  obtain ⟨γ, hγa, hγb, hγ, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfinite
      (by linarith : t - 1 < t)
  have hi := hM06.ancient_integrated n M K.flow K.complete
    K.nonnegative_curvature_operator (K.operator_bound hM04) K.nonflat
    (t - 1) t (by linarith) ht γ hγ.contMDiffOn p x hγa hγb
  exact (mul_pos hscalar (Real.exp_pos _)).trans_le hi

theorem scalar_derivative_nonnegative (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u}) (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0) (x : M) :
    ∃ dR : ℝ, HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
      dR (Iic 0) t ∧ 0 ≤ dR := by
  obtain ⟨dR, hdR, hineq⟩ := hM06.ancient_differential n M K.flow K.complete
    K.nonnegative_curvature_operator (K.operator_bound hM04) K.nonflat t ht x 0
  refine ⟨dR, hdR, ?_⟩
  have hzero : (K.flow.connection t).ricci x 0 0 = 0 := by
    rw [(K.flow.connection t).ricci_eq_sum_frame x 0 0]
    simp
  simpa only [hzero, map_zero, mul_zero, add_zero] using hineq

theorem scalar_monotone (hM04 : RicciFlowCurvatureTheory.{u})
    (hM06 : HarnackAncientTheory.{u}) (K : AncientKappaSolution n M)
    (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 0) (x : M) :
    (K.flow.connection s).scalarCurvature x ≤ (K.flow.connection t).scalarCurvature x := by
  classical
  have hm : MonotoneOn (fun t => (K.flow.connection t).scalarCurvature x) (Iic 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0)
      (fun t ht => (K.scalar_derivative_nonnegative hM04 hM06 t ht x).choose_spec.1.continuousWithinAt)
      (f' := fun t => if ht : t ≤ 0 then
        (K.scalar_derivative_nonnegative hM04 hM06 t ht x).choose else 0)
    · intro t ht
      have ht' : t ∈ Iic (0 : ℝ) := interior_subset ht
      simpa only [dif_pos (show t ≤ 0 from ht')] using
        (K.scalar_derivative_nonnegative hM04 hM06 t ht' x).choose_spec.1.mono
          (show interior (Iic (0 : ℝ)) ⊆ Iic 0 from interior_subset)
    · intro t ht
      have ht' : t ∈ Iic (0 : ℝ) := interior_subset ht
      simpa only [dif_pos (show t ≤ 0 from ht')] using
        (K.scalar_derivative_nonnegative hM04 hM06 t ht' x).choose_spec.2
  exact hm (hst.trans ht) ht hst

theorem ricci_bounds (hM04 : RicciFlowCurvatureTheory.{u})
    (K : AncientKappaSolution n M) (t : ℝ) (ht : t ≤ 0) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    0 ≤ (K.flow.connection t).ricci x v v ∧
      (K.flow.connection t).ricci x v v ≤
        (K.flow.connection t).scalarCurvature x * (K.flow.metric t).inner x v v :=
  (K.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
    (hM04.tensor_calculus n M _ _) x (K.nonnegative_curvature_operator t ht x) v

theorem metric_monotone (hM04 : RicciFlowCurvatureTheory.{u})
    (K : AncientKappaSolution n M) (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (K.flow.metric t).inner x v v ≤ (K.flow.metric s).inner x v v := by
  have hm : AntitoneOn (fun t => (K.flow.metric t).inner x v v) (Iic 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0)
      (fun t ht => (K.flow.equation t ht x v v).continuousWithinAt)
      (f' := fun t => -2 * (K.flow.connection t).ricci x v v)
    · intro t ht
      exact (K.flow.equation t (interior_subset ht) x v v).mono interior_subset
    · intro t ht
      exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (K.ricci_bounds hM04 t (show t ∈ Iic (0 : ℝ) from interior_subset ht) x v).1
  exact hm (hst.trans ht) ht hst

theorem edist_monotone (hM04 : RicciFlowCurvatureTheory.{u})
    (K : AncientKappaSolution n M) (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 0) (x y : M) :
    (K.flow.metric t).edist x y ≤ (K.flow.metric s).edist x y := by
  have h := RiemannianMetric.edist_le_mul_of_inner_mfderiv_le
    (K.flow.metric s) (K.flow.metric t) (F := id) contMDiff_id
    (C := 1) zero_lt_one (fun z v => by
      simpa using K.metric_monotone hM04 s t hst ht z v) x y
  simpa using h

end PoincareConjecture.AncientKappaSolution
