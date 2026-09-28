import PoincareConjecture.Proofs.M09.ExponentialCoercivity
import Mathlib.Analysis.Normed.Group.Bounded








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_action_bound_near_zero {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) (a : ℝ) (_ha : 0 ≤ a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Z : TangentSpace (𝓡 n) p),
      (F.metric T).tangentNorm p Z ≤ a → ∀ t, 0 < t → t ≤ b →
        |A.action Z t| ≤ D * Real.sqrt t := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  letI : FiniteDimensional ℝ E :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  let K := Metric.closedBall (0 : E) a ×ˢ Set.Icc 0 (Real.sqrt b)
  let U := A.squareDomain ∩ (Set.univ ×ˢ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
  let f : E × ℝ → M := fun z ↦ A.squareFamily z.1 z.2
  let H := squareFamilyActionDensity F T f
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hU : IsOpen U := A.square_open.inter (isOpen_univ.prod isOpen_Ioo)
  have hKU : K ⊆ U := by
    intro z hz
    have hlt := hz.2.2.trans_lt (Real.sqrt_lt_sqrt hb.le hbmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hz.2.1, hlt⟩,
      Set.mem_univ _, (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hz.2.1, hlt⟩
  have hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f A.squareDomain := by
    convert! A.square_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hH : ContDiffOn ℝ ∞ H U :=
    squareFamilyActionDensity_contDiffOn F hM04 T τmax hτmax hwindow f U hU
      (hf.mono Set.inter_subset_left) (fun z hz ↦ hz.2.2)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hH.continuousOn.mono hKU)
  refine ⟨max 0 D, le_max_left _ _, ?_⟩
  intro Z hZ t ht htb
  have hZn : ‖Z‖ ≤ a := by
    rw [norm_eq_sqrt_real_inner]
    exact hZ
  rw [lExponentialFamily_action_square_eq A Z t ht (htb.trans_lt hbmax)]
  have hbound : ∀ s ∈ Set.uIoc 0 (Real.sqrt t), ‖H (Z, s)‖ ≤ max 0 D := by
    intro s hs
    rw [Set.uIoc_of_le (Real.sqrt_nonneg t)] at hs
    exact (hD (Z, s) ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hZn,
      hs.1.le, hs.2.trans (Real.sqrt_le_sqrt htb)⟩).trans (le_max_right _ _)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (Real.sqrt_nonneg t)] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

theorem lExponentialFamily_minimizing_competitors_bounded [ConnectedSpace M]
    [T3Space M] [SecondCountableTopology M] {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (p : M) (A : LExponentialFamily F T τmax p)
    (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) (a : ℝ) (ha : 0 ≤ a) :
    ∃ R : ℝ, 0 ≤ R ∧ a ≤ R ∧ ∀ Z : TangentSpace (𝓡 n) p,
      (F.metric T).tangentNorm p Z ≤ a → ∀ t (ht : 0 < t) (htb : t ≤ b),
      ∀ W : TangentSpace (𝓡 n) p, A.gamma W t = A.gamma Z t →
        IsMinimizingBackwardLPath F T 0 t (A.path W t ht (htb.trans_lt hbmax)) →
          (F.metric T).tangentNorm p W ≤ R := by
  obtain ⟨D, hD, hbound⟩ := lExponentialFamily_action_bound_near_zero hM04 hτmax
    hwindow A b hb hbmax a ha
  obtain ⟨B, C, hB, hC, hcoercive⟩ := exists_uniform_lExponentialFamily_action_coercive
    F hM04 T τmax hτmax hwindow hcurvature b hb hbmax
  let K := Real.exp (B * Real.sqrt b) * (2 * D + 4 * C * b + 1)
  refine ⟨max a (Real.sqrt K), ha.trans (le_max_left _ _), le_max_left _ _, ?_⟩
  intro Z hZ t ht htb W hend hmin
  have hmax := htb.trans_lt hbmax
  have hcompare : A.action W t ≤ A.action Z t := by
    have h := hmin (A.path Z t ht hmax)
      (by simp only [A.path_eq, A.gamma_at_zero])
      (by simpa only [A.path_eq] using hend.symm)
    simpa only [A.path_eq, LExponentialFamily.action] using h
  have haction : A.action W t ≤ D * Real.sqrt t :=
    hcompare.trans ((le_abs_self _).trans (hbound Z hZ t ht htb))
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have henergy : 0 ≤ (F.metric T).inner p W W := by
    rcases eq_or_ne W 0 with rfl | hne
    · simp
    · exact ((F.metric T).pos p W hne).le
  have hupper : 4 * (F.metric T).inner p W W + 1 ≤
      Real.exp (B * Real.sqrt t) * (2 * D + 4 * C * t + 1) := by
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ Real.exp (B * Real.sqrt t) *
          (2 * A.action W t + 4 * C * (Real.sqrt t) ^ 3 + Real.sqrt t) :=
        hcoercive p A W t ht htb
      _ ≤ Real.exp (B * Real.sqrt t) *
          (2 * (D * Real.sqrt t) + 4 * C * (Real.sqrt t) ^ 3 + Real.sqrt t) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        linarith
      _ = Real.sqrt t *
          (Real.exp (B * Real.sqrt t) * (2 * D + 4 * C * t + 1)) := by
        have hcub : (Real.sqrt t) ^ 3 = Real.sqrt t * t := by
          calc
            _ = Real.sqrt t * (Real.sqrt t) ^ 2 := by ring
            _ = Real.sqrt t * t := by rw [Real.sq_sqrt ht.le]
        rw [hcub]
        ring
  have hconstant : Real.exp (B * Real.sqrt t) * (2 * D + 4 * C * t + 1) ≤ K := by
    apply mul_le_mul
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htb) hB.le)
    · have hc := mul_le_mul_of_nonneg_left htb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hC)
      linarith
    · positivity
    · exact Real.exp_nonneg _
  have heK : (F.metric T).inner p W W ≤ K := by
    linarith [hupper.trans hconstant]
  exact (Real.sqrt_le_sqrt heK).trans (le_max_right _ _)

end PoincareConjecture.Proofs.M09
