import PoincareConjecture.Proofs.M09.IntrinsicEnergyBound

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem initialMetric_inner_le_window {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b K : ℝ)
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hwindow : Set.Icc (T - b) T ⊆ J)
    (hbound : ∀ s ∈ Set.Icc (T - b) T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (T - b) T)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric T).inner x v v ≤
      Real.exp (2 * (n : ℝ) * K * b) * (F.metric t).inner x v v := by
  have hlo := (window_metric_comparison F hM04 T b K hb hK hwindow hbound t ht x v).1
  calc
    _ = Real.exp (2 * (n : ℝ) * K * b) *
        (Real.exp (-(2 * (n : ℝ) * K * b)) * (F.metric T).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Real.exp_nonneg _)

theorem exists_uniform_initialMetric_speed_bound {J : Set ℝ}
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (b Emax : ℝ) (hb : 0 < b) (hbmax : b < τmax) (hEmax : 0 ≤ Emax) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ → M) (U : Set ℝ) (h : ℝ),
      0 ≤ h → h < Real.sqrt b → IsOpen U → Set.Icc 0 h ⊆ U →
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U →
      ∀ E : ParametricAlongCurveExtensionOn (n := n) (Set.Icc 0 h) γ
        (curveVelocityWithin (n := n) γ (Set.Icc 0 h)),
      (∀ s ∈ Set.Icc 0 h, regularizedLGeodesicEquation F T γ (Set.Icc 0 h) E s) →
      regularizedCurveEnergy F T γ 0 ≤ Emax →
      ∀ s ∈ Set.Icc 0 h,
        (F.metric T).tangentNorm (γ s) (curveVelocity γ s) ≤ C := by
  obtain ⟨A, hA, henergy⟩ := exists_uniform_regularizedCurveEnergy_exp_bound
    F hM04 T τmax hτmax hwindow hcurvature b hb hbmax
  obtain ⟨K, hK, hcurv⟩ := hcurvature.2
  let D : ℝ := 2 * (n : ℝ) * K * τmax
  let Q : ℝ := Real.exp D * ((Emax + 1) * Real.exp (A * Real.sqrt b))
  refine ⟨Real.sqrt Q + 1, by positivity, ?_⟩
  intro γ U h hh hhb hU hIU hγ E heq hE s hs
  have he := henergy γ U h hh hhb hU hIU hγ E heq s hs
  have hsqrt : s ≤ Real.sqrt b := hs.2.trans hhb.le
  have hs2 : s ^ 2 ≤ b := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b, hs.1]
  have ht : T - s ^ 2 ∈ Set.Icc (T - τmax) T :=
    ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩
  have he' : regularizedCurveEnergy F T γ s ≤
      (Emax + 1) * Real.exp (A * Real.sqrt b) := by
    have h1 := mul_le_mul_of_nonneg_right (add_le_add_right hE 1) (Real.exp_nonneg (A * s))
    have h2 := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt hA.le))
      (by linarith : 0 ≤ Emax + 1)
    linarith [h1, h2]
  have hmetric := initialMetric_inner_le_window F hM04 T τmax K hτmax.le hK hwindow
    (fun t ht x ↦ (le_abs_self _).trans (hcurv t ht x)) (T - s ^ 2) ht
    (γ s) (curveVelocity γ s)
  have hquadratic : (F.metric T).inner (γ s) (curveVelocity γ s) (curveVelocity γ s) ≤ Q :=
    hmetric.trans (mul_le_mul_of_nonneg_left he' (Real.exp_nonneg D))
  exact (Real.sqrt_le_sqrt hquadratic).trans (by linarith)

end PoincareConjecture.Proofs.M09
