import PoincareConjecture.Proofs.M08.CompleteFlowDerivativeBound
import PoincareConjecture.Proofs.M08.ScalarTraceDerivative
import PoincareConjecture.Proofs.M08.ContinuationSpeed
import PoincareConjecture.Proofs.M08.ReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1500000 in

theorem exists_uniform_continuation_referenceSpeedSq_bound {J : Set ℝ}
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax c : ℝ) (hc : 0 < c) (hcm : c ^ 2 < τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T)) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a b : ℝ) (α : ℝ → M),
      0 ≤ a → a < c → c < b →
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (Ioo a b) →
      (∀ r ∈ Ioo a b, T - r ^ 2 ∈ J) →
      ∀ E : ParametricAlongCurveExtensionOn (Ioo a b) α
          (curveVelocityWithin (n := n) α (Ioo a b)),
      (∀ r ∈ Ioo a b, regularizedLGeodesicEquation F T α (Ioo a b) E r) →
      ∀ s ∈ Ioc a c, referenceSpeedSq (F.metric T) α s ≤
        D * (continuationSpeedSq F T α (Ioo a b) c + 1) := by
  obtain ⟨K, hK, hRm⟩ := hcurvature.2
  obtain ⟨B, hB, hgrad⟩ := exists_uniform_curvatureDerivative_bound F hM04 T τmax
    (c ^ 2) ((sq_nonneg c).trans_lt hcm) hcm hwindow hcurvature
  let C := 4 * c ^ 2 * (n : ℝ) ^ 3 * B + 4 * c * (n : ℝ) ^ 3 * K
  let D := Real.exp (2 * (n : ℝ) * K * τmax) * Real.exp (C * c)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro a b α ha hac hcb hα htime E heq s hs
  let U := Ioo a b
  let A := curveVelocityWithin (n := n) α U
  let q := continuationSpeedSq F T α U
  let R := fun r ↦ scalarCurvatureDifferential F (fun t ↦ T - t ^ 2) α r (A r)
  let Ric := fun r ↦ (F.connection (T - r ^ 2)).ricci (α r) (A r) (A r)
  let q' := fun r ↦ 4 * r ^ 2 * R r - 4 * r * Ric r
  have hqnonneg (r : ℝ) : 0 ≤ q r := continuationSpeedSq_nonneg F T α U r
  have hsub : Icc s c ⊆ Ioo a b := by
    intro r hr
    exact ⟨hs.1.trans_le hr.1, hr.2.trans_lt hcb⟩
  have hqcont : ContinuousOn q (Icc s c) :=
    (continuationSpeedSq_contDiffOn F T α (uniqueDiffOn_Ioo a b) isOpen_Ioo
      subset_rfl hα htime).continuousOn.mono hsub
  have hqd (r : ℝ) (hr : r ∈ Ioo s c) : HasDerivAt q (q' r) r := by
    have hrU := hsub (Ioo_subset_Icc_self hr)
    have h := continuationSpeedSq_hasDerivAt F hM04 T α (uniqueDiffOn_Ioo a b)
      isOpen_Ioo subset_rfl hα htime E hrU (isOpen_Ioo.mem_nhds hrU)
    have he := heq r hrU (A r)
    unfold regularizedEulerResidual at he
    convert h using 1 <;> dsimp only [q', R, Ric, A, U] at he ⊢ <;> linarith
  have hbound (r : ℝ) (hr : r ∈ Ioo s c) : -(C * (q r + 1)) ≤ q' r := by
    have hr0 : 0 ≤ r := ha.trans (hs.1.trans hr.1).le
    have hrsq : r ^ 2 ≤ c ^ 2 := by nlinarith [hr.2]
    have htimeR : T - r ^ 2 ∈ Icc (T - τmax) T :=
      ⟨by linarith [hrsq], sub_le_self T (sq_nonneg r)⟩
    have hR : |R r| ≤ (n : ℝ) ^ 3 * B * Real.sqrt (q r) := by
      have h := scalarCurvature_differential_abs_le hM04
        (F.connection (T - r ^ 2)) (α r) (A r)
      change |R r| ≤ (n : ℝ) ^ 3 *
        (F.connection (T - r ^ 2)).curvatureDerivativeNorm 1 (α r) * Real.sqrt (q r) at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgrad (r ^ 2) ⟨sq_nonneg r, hrsq⟩ (α r))
          (by positivity)) (Real.sqrt_nonneg _))
    have hRic : |Ric r| ≤ (n : ℝ) ^ 3 * K * q r := by
      have h := ricci_quadratic_abs_le hM04 (F.connection (T - r ^ 2)) (α r) (A r)
      change |Ric r| ≤ (n : ℝ) ^ 3 *
        (F.connection (T - r ^ 2)).curvatureTensorNorm (α r) * q r at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hRm _ htimeR (α r)))
          (by positivity)) (hqnonneg r))
    have hsqrt : Real.sqrt (q r) ≤ q r + 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · linarith [hqnonneg r]
      · nlinarith [hqnonneg r, sq_nonneg (q r)]
    have hRterm : 4 * r ^ 2 * |R r| ≤
        (4 * c ^ 2 * (n : ℝ) ^ 3 * B) * (q r + 1) := by
      calc
        _ ≤ 4 * r ^ 2 * ((n : ℝ) ^ 3 * B * Real.sqrt (q r)) :=
          mul_le_mul_of_nonneg_left hR (by positivity)
        _ = (4 * r ^ 2 * (n : ℝ) ^ 3 * B) * Real.sqrt (q r) := by ring
        _ ≤ _ := mul_le_mul (by gcongr) hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hRicterm : 4 * r * |Ric r| ≤
        (4 * c * (n : ℝ) ^ 3 * K) * (q r + 1) := by
      calc
        _ ≤ 4 * r * ((n : ℝ) ^ 3 * K * q r) :=
          mul_le_mul_of_nonneg_left hRic (by positivity)
        _ = (4 * r * (n : ℝ) ^ 3 * K) * q r := by ring
        _ ≤ _ := mul_le_mul (by gcongr; exact hr.2.le) (by linarith)
          (hqnonneg r) (by positivity)
    calc
      -(C * (q r + 1)) = -((4 * c ^ 2 * (n : ℝ) ^ 3 * B) * (q r + 1) +
          (4 * c * (n : ℝ) ^ 3 * K) * (q r + 1)) := by dsimp only [C]; ring
      _ ≤ -(4 * r ^ 2 * |R r| + 4 * r * |Ric r|) :=
        neg_le_neg (add_le_add hRterm hRicterm)
      _ ≤ q' r := by
        dsimp only [q']
        have h₁ := mul_le_mul_of_nonneg_left (neg_abs_le (R r))
          (by positivity : 0 ≤ 4 * r ^ 2)
        have h₂ := mul_le_mul_of_nonneg_left (le_abs_self (Ric r))
          (by positivity : 0 ≤ 4 * r)
        linarith
  have hqbound : q s ≤ Real.exp (C * c) * (q c + 1) :=
    backward_gronwall_uniform_bound (ha.trans hs.1.le) hC (hqnonneg c)
      hqcont hqd hbound ⟨le_rfl, hs.2⟩
  have hsU := hsub ⟨le_rfl, hs.2⟩
  have hA : A s = curveVelocity (n := n) α s := by
    simp only [A, U, curveVelocityWithin, curveVelocity,
      mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hsU)]
  have hssq : s ^ 2 ≤ τmax := by
    have hs0 := ha.trans hs.1.le
    nlinarith [hs.2]
  have hcomp := (backwardPath_metric_comparison (τ₁ := 0) (τ₂ := s ^ 2)
    hM04 hwindow le_rfl (sq_nonneg s) hssq hK hRm (α s) (A s)).2
  simp only [sub_zero] at hcomp
  calc
    referenceSpeedSq (F.metric T) α s = (F.metric T).inner (α s) (A s) (A s) := by
      rw [hA]
      rfl
    _ ≤ Real.exp (2 * (n : ℝ) * K * s ^ 2) * q s := hcomp
    _ ≤ Real.exp (2 * (n : ℝ) * K * τmax) * q s := by
      apply mul_le_mul_of_nonneg_right _ (hqnonneg s)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hssq (by positivity)
    _ ≤ Real.exp (2 * (n : ℝ) * K * τmax) *
        (Real.exp (C * c) * (q c + 1)) :=
      mul_le_mul_of_nonneg_left hqbound (Real.exp_pos _).le
    _ = D * (continuationSpeedSq F T α (Ioo a b) c + 1) := by
      dsimp only [D, q, U]
      ring

end PoincareConjecture.M08
