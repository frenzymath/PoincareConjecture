import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Comparison.Jets.ComparisonCovariantJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.BilinearJets

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private theorem exists_coordinate_frame_norm_bound (g : RiemannianMetric 3 E) (x : E) :
    ∃ c : ℝ, 0 < c ∧ ∀ i : Fin 3, g.tangentNorm x (e i) ≤ c := by
  let c : ℝ := 1 + ∑ i : Fin 3, g.tangentNorm x (e i)
  have hsum : 0 ≤ ∑ i : Fin 3, g.tangentNorm x (e i) :=
    Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  refine ⟨c, by dsimp [c]; linarith, ?_⟩
  intro i
  have h := Finset.single_le_sum (fun j _ => Real.sqrt_nonneg
    (g.inner x (e j) (e j))) (Finset.mem_univ i)
  change g.tangentNorm x (e i) ≤ ∑ j : Fin 3, g.tangentNorm x (e j) at h
  dsimp [c]
  linarith

theorem exists_tensor_coordinate_jet_bound
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E) (k j m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : CovariantTensorEvaluation 3 E k),
      IsSmoothCovariantTensor T → ∀ ρ : ℝ, 0 ≤ ρ →
      (∀ r ≤ j + m, g.tensorNorm (D.iteratedCovariantTensorDerivative T r) x ≤ ρ) →
      ∀ a : Fin (k + m) → Fin 3,
        ‖iteratedFDeriv ℝ j
          (comparisonTensorComponent (D.iteratedCovariantTensorDerivative T m) a) x‖ ≤
            C * ρ := by
  classical
  induction j using Nat.strong_induction_on generalizing m with
  | h j ih =>
      cases j with
      | zero =>
          obtain ⟨c, hc, hframe⟩ := exists_coordinate_frame_norm_bound g x
          refine ⟨c ^ (k + m), pow_pos hc _, ?_⟩
          intro T hT ρ hρ hbound a
          rw [norm_iteratedFDeriv_zero]
          obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth hT m).1 x
          have h := abs_tensor_evaluation_le_tensorNorm g _ x A hA (fun i => e (a i))
          have hp : (∏ i : Fin (k + m), g.tangentNorm x (e (a i))) ≤ c ^ (k + m) := by
            calc
              _ ≤ ∏ _i : Fin (k + m), c :=
                Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) (fun i _ => hframe (a i))
              _ = _ := by simp
          exact h.trans ((mul_le_mul (hbound m (by omega)) hp
            (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) hρ).trans_eq (mul_comm _ _))
      | succ j =>
          obtain ⟨A, hA, hAbound⟩ := ih j (Nat.lt_succ_self j) (m + 1)
          choose B hB hBbound using fun l : Fin (j + 1) => ih l l.isLt m
          choose G hG hGbound using fun l : Fin (j + 1) =>
            exists_comparisonChristoffel_jet_bound g (K := {x}) isCompact_singleton l
          let B0 : ℝ := 1 + ∑ l : Fin (j + 1), B l
          have hB0 : 0 < B0 := by
            have hsum : 0 ≤ ∑ l : Fin (j + 1), B l :=
              Finset.sum_nonneg (fun l _ => (hB l).le)
            dsimp [B0]
            linarith
          have hBle (l : Fin (j + 1)) : B l ≤ B0 := by
            have h := Finset.single_le_sum (fun z _ => (hB z).le) (Finset.mem_univ l)
            dsimp [B0]
            linarith
          let S : ℝ := ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * B0
          have hS : 0 ≤ S := by
            apply Finset.sum_nonneg
            intro l _
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hG l).le) hB0.le
          refine ⟨3 * (A + 3 * (k + m : ℕ) * S), by positivity, ?_⟩
          intro T hT ρ hρ hbound a
          let Tm := D.iteratedCovariantTensorDerivative T m
          have hTm : IsSmoothCovariantTensor Tm :=
            D.iteratedCovariantTensorDerivative_isSmooth hT m
          have hlow (l : ℕ) (hl : l ≤ j) (b : Fin (k + m) → Fin 3) :
              ‖iteratedFDeriv ℝ l (comparisonTensorComponent Tm b) x‖ ≤ B0 * ρ := by
            let l' : Fin (j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
            exact (hBbound l' T hT ρ hρ (fun r hr => hbound r (by
              dsimp [l'] at hr
              omega)) b).trans (mul_le_mul_of_nonneg_right (hBle l') hρ)
          have hproduct (i b c : Fin 3) (a : Fin (k + m) → Fin 3) :
              ‖iteratedFDeriv ℝ j (fun p => comparisonChristoffel g b i c p *
                comparisonTensorComponent Tm a p) x‖ ≤ S * ρ := by
            have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
              (x := x) (comparisonChristoffel_contDiff g b i c).contDiffAt
              (comparisonTensorComponent_contDiff hTm a).contDiffAt j
            simp only [smul_eq_mul] at h
            apply h.trans
            rw [← Fin.sum_univ_eq_sum_range]
            calc
              _ ≤ ∑ l : Fin (j + 1), (j.choose l : ℝ) * G l * (B0 * ρ) := by
                apply Finset.sum_le_sum
                intro l _
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (hGbound l b i c x (mem_singleton x))
                    (Nat.cast_nonneg _)
                · exact hlow (j - l) (Nat.sub_le _ _) a
                · exact norm_nonneg _
                · exact mul_nonneg (Nat.cast_nonneg _) (hG l).le
              _ = S * ρ := by simp only [S, Finset.sum_mul, mul_assoc]
          have hdirection (i : Fin 3) :
              ‖iteratedFDeriv ℝ j (fun p =>
                fderiv ℝ (comparisonTensorComponent Tm a) p (e i)) x‖ ≤
                  (A + 3 * (k + m : ℕ) * S) * ρ := by
            let Q (l : Fin (k + m)) (b : Fin 3) (p : E) :=
              comparisonChristoffel g b i (a l) p *
                comparisonTensorComponent Tm (Function.update a l b) p
            have hQ (l : Fin (k + m)) (b : Fin 3) : ContDiffAt ℝ ∞ (Q l b) x :=
              (comparisonChristoffel_contDiff g b i (a l)).contDiffAt.mul
                (comparisonTensorComponent_contDiff hTm _).contDiffAt
            have hsumSmooth : ContDiffAt ℝ ∞ (fun p => ∑ l, ∑ b, Q l b p) x :=
              ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun b _ => hQ l b))
            have hsum : ‖iteratedFDeriv ℝ j (fun p => ∑ l, ∑ b, Q l b p) x‖ ≤
                3 * (k + m : ℕ) * S * ρ := by
              calc
                _ ≤ ∑ l : Fin (k + m),
                    ‖iteratedFDeriv ℝ j (fun p => ∑ b, Q l b p) x‖ :=
                  norm_iteratedFDeriv_finite_sum _
                    (fun l => ContDiffAt.sum (fun b _ => hQ l b)) j
                _ ≤ ∑ l : Fin (k + m), ∑ b : Fin 3,
                    ‖iteratedFDeriv ℝ j (Q l b) x‖ :=
                  Finset.sum_le_sum (fun l _ => norm_iteratedFDeriv_finite_sum _ (hQ l) j)
                _ ≤ ∑ _l : Fin (k + m), ∑ _b : Fin 3, S * ρ :=
                  Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun b _ =>
                    hproduct i b (a l) (Function.update a l b)))
                _ = _ := by simp; ring
            have heq : (fun p => fderiv ℝ (comparisonTensorComponent Tm a) p (e i)) =
                fun p => comparisonTensorComponent
                  (D.iteratedCovariantTensorDerivative T (m + 1)) (Fin.cons i a) p +
                    ∑ l, ∑ b, Q l b p := by
              funext p
              have h := comparisonTensorComponent_covariant D hTm (Fin.cons i a) p
              simpa only [Fin.cons_zero, Fin.cons_succ, Tm,
                LeviCivitaData.iteratedCovariantTensorDerivative, Q] using (eq_sub_iff_add_eq.mp h).symm
            rw [heq, fun_iteratedFDeriv_add_apply
              ((comparisonTensorComponent_contDiff
                (D.iteratedCovariantTensorDerivative_isSmooth hT (m + 1)) _).contDiffAt.of_le
                  (by exact_mod_cast le_top))
              (hsumSmooth.of_le (by exact_mod_cast le_top))]
            exact (norm_add_le _ _).trans
              ((add_le_add (hAbound T hT ρ hρ (fun r hr => hbound r (by omega)) _)
                hsum).trans_eq (by ring))
          calc
            _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ j (fun p =>
                fderiv ℝ (comparisonTensorComponent Tm a) p (e i)) x‖ :=
              norm_iteratedFDeriv_succ_le_basis (comparisonTensorComponent_contDiff hTm a).contDiffAt j
            _ ≤ ∑ _i : Fin 3, (A + 3 * (k + m : ℕ) * S) * ρ :=
              Finset.sum_le_sum (fun i _ => hdirection i)
            _ = _ := by simp; ring

theorem exists_bilinear_coordinate_jet_bound
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : E → Bilin), ContDiff ℝ ∞ B →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (∀ r ≤ m, g.tensorNorm (D.iteratedCovariantTensorDerivative (k := 2)
        (fun y v => B y (v 0) (v 1)) r) x ≤ ρ) →
      ‖iteratedFDeriv ℝ m B x‖ ≤ C * ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_tensor_coordinate_jet_bound D x 2 m 0
  refine ⟨9 * C, by positivity, ?_⟩
  intro B hB ρ hρ hnorm
  have hcomponents (a b : Fin 3) :
      ‖iteratedFDeriv ℝ m (fun y => B y (e a) (e b)) x‖ ≤ C * ρ := by
    exact hbound _ (comparison_bilinear_isSmooth hB) ρ hρ
      (by simpa only [Nat.add_zero] using hnorm) ![a, b]
  have h := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components
    e hB.contDiffAt m hcomponents
  norm_num only [Fintype.card_fin] at h
  exact h.trans_eq (by ring)

end PoincareConjecture.SingularRegularLimit.RoundComparison
