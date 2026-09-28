import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction
import PoincareConjecture.Proofs.M14.Sec6_1_PathCongruence
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalCoherence











set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}



noncomputable def initialValueAction (G : GeneralizedLGeometryTransport n X time I)
    (T : ℝ) (x : G.Point) (Z : G.Horizontal x) (s : ℝ) : ℝ := by
  classical
  exact if h : initialValueSurvives G T x Z s then
    M14BackwardLAction G (selectedInitialValuePath h).path else 0

variable {G : GeneralizedLGeometryTransport n X time I} {T τ : ℝ}
  {x y y' : G.Point} {Z : G.Horizontal x}



theorem initialValueAction_zero (Z : G.Horizontal x) : initialValueAction G T x Z 0 = 0 := by
  unfold initialValueAction
  rw [dif_neg (show ¬ initialValueSurvives G T x Z 0 from fun h => (lt_irrefl 0) h.1)]




theorem initialValuePath_action_eq
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    (Q : M14SquareRootInitialValuePath G T τ x y' Z) :
    M14BackwardLAction G P.path = M14BackwardLAction G Q.path := by
  have hy := initialValuePath_endpoint_eq hM04 hM12 P Q
  subst y'
  apply action_eq_of_curve_eqOn P.path Q.path
  intro r hr
  apply initialValuePath_curve_eqOn hM04 hM12 P Q
  simpa only [min_self] using Ioo_subset_Icc_self hr




theorem initialValueAction_eq_of_path
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {s : ℝ} (hs : 0 < s) (P : M14SquareRootInitialValuePath G T (s ^ 2) x y Z) :
    initialValueAction G T x Z s = M14BackwardLAction G P.path := by
  have hsurv : initialValueSurvives G T x Z s := ⟨hs, y, ⟨P⟩⟩
  unfold initialValueAction
  rw [dif_pos hsurv]
  exact initialValuePath_action_eq hM04 hM12 (selectedInitialValuePath hsurv) P




theorem initialValueAction_eq_integral_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) {r : ℝ}
    (hr : r ∈ Icc 0 (Real.sqrt τ)) :
    initialValueAction G T x Z r = ∫ s in 0..r, squareRootLIntegrand P.square_path s := by
  rcases eq_or_lt_of_le hr.1 with hr₀ | hr₀
  · subst r
    rw [initialValueAction_zero, intervalIntegral.integral_same]
  · have hsq : r ^ 2 ≤ τ := (sq_le_sq₀ hr₀.le (Real.sqrt_nonneg τ)).mpr hr.2 |>.trans_eq
      (Real.sq_sqrt P.path.tau_lt.le)
    let Q := initialValuePathRestrict P (sq_pos_of_pos hr₀) hsq
    rw [initialValueAction_eq_of_path hM04 hM12 hr₀ Q,
      ← integral_squareRootLIntegrand_eq_action Q.square_path, Real.sqrt_zero,
      Real.sqrt_sq hr₀.le]
    rfl

end PoincareConjecture.M14
