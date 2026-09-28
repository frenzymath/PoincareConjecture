import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.Jets.CylinderAllOrder
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Operations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.MetricSurgery

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def centeredCylinderChristoffelJetBound (j : ℕ) : ℝ :=
  1 + ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖

theorem centeredCylinderChristoffelJetBound_pos (j : ℕ) :
    0 < centeredCylinderChristoffelJetBound j := by
  unfold centeredCylinderChristoffelJetBound
  positivity

theorem centeredCylinderChristoffel_jet_bound (j : ℕ) (a b c : Fin 3) :
    ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖ ≤
      centeredCylinderChristoffelJetBound j := by
  have hc : ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖ ≤
      ∑ c : Fin 3, ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖ :=
    Finset.single_le_sum
      (f := fun c : Fin 3 => ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  have hb : (∑ c : Fin 3, ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖) ≤
      ∑ b : Fin 3, ∑ c : Fin 3,
        ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖ :=
    Finset.single_le_sum
      (f := fun b : Fin 3 => ∑ c : Fin 3,
        ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.mem_univ b)
  have ha : (∑ b : Fin 3, ∑ c : Fin 3,
        ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖) ≤
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖ :=
    Finset.single_le_sum
      (f := fun a : Fin 3 => ∑ b : Fin 3, ∑ c : Fin 3,
        ‖iteratedFDeriv ℝ j (centeredCylinderChristoffel a b c) 0‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => norm_nonneg _))) (Finset.mem_univ a)
  exact (hc.trans (hb.trans ha)).trans (by
    unfold centeredCylinderChristoffelJetBound
    linarith)



theorem exists_centeredCylinderComponent_jet_bound (j k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {epsilon : ℝ}, 0 < epsilon →
      ∀ {B : RoundCylinderTwoTensor}, RoundCylinderClose epsilon 0 B →
      j + k ≤ ⌊epsilon⁻¹⌋₊ →
      ∀ z : RoundCylinderSpace,
        z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
        ∀ a : Fin (2 + k) → Fin 3,
          ‖iteratedFDeriv ℝ j
            (centeredCylinderComponent B z.1 z.2 k a) 0‖ ≤ C * epsilon := by
  classical
  induction j using Nat.strong_induction_on generalizing k with
  | h j ih =>
      cases j with
      | zero =>
          refine ⟨Real.sqrt ((2 : ℝ) ^ (2 + k)), by positivity, ?_⟩
          intro epsilon hepsilon B hB horder z hz a
          rw [norm_iteratedFDeriv_zero]
          exact centeredCylinderComponent_center_bound hepsilon.le hB
            (by simpa using horder) z hz a
      | succ j =>
          obtain ⟨A, hA, hAbound⟩ := ih j (Nat.lt_succ_self j) (k + 1)
          choose D hD hDbound using fun l : Fin (j + 1) => ih l l.isLt k
          let D0 : ℝ := 1 + ∑ l : Fin (j + 1), D l
          have hD0 : 0 < D0 := by
            dsimp [D0]
            have hsum : 0 ≤ ∑ l : Fin (j + 1), D l :=
              Finset.sum_nonneg (fun l _ => (hD l).le)
            linarith
          have hDle (l : Fin (j + 1)) : D l ≤ D0 := by
            have h := Finset.single_le_sum (fun m _ => (hD m).le) (Finset.mem_univ l)
            dsimp [D0]
            linarith
          let S : ℝ := ∑ l ∈ Finset.range (j + 1),
            (j.choose l : ℝ) * centeredCylinderChristoffelJetBound l * D0
          have hS : 0 ≤ S := by
            apply Finset.sum_nonneg
            intro l _
            exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
              (centeredCylinderChristoffelJetBound_pos l).le) hD0.le
          refine ⟨3 * (A + 3 * (2 + (k : ℝ)) * S), by positivity, ?_⟩
          intro epsilon hepsilon B hB horder z hz a
          have hcomponent (k : ℕ) (a : Fin (2 + k) → Fin 3) :=
            centeredCylinderComponent_contDiffAt hB z hz k a
          have hlow (l : ℕ) (hl : l ≤ j) (a : Fin (2 + k) → Fin 3) :
              ‖iteratedFDeriv ℝ l (centeredCylinderComponent B z.1 z.2 k a) 0‖ ≤
                D0 * epsilon := by
            let l' : Fin (j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
            exact (hDbound l' hepsilon hB (by dsimp [l']; omega) z hz a).trans
              (mul_le_mul_of_nonneg_right (hDle l') hepsilon.le)
          have hproduct (i b c : Fin 3) (a : Fin (2 + k) → Fin 3) :
              ‖iteratedFDeriv ℝ j (fun p => centeredCylinderChristoffel b i c p *
                centeredCylinderComponent B z.1 z.2 k a p) 0‖ ≤ S * epsilon := by
            have h := Poincare.Analysis.Calculus.norm_iteratedFDeriv_smul_le_of_contDiffAt
              (centeredCylinderChristoffel_contDiff b i c).contDiffAt (hcomponent k a) j
            simp only [smul_eq_mul] at h
            apply h.trans
            calc
              _ ≤ ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) *
                  centeredCylinderChristoffelJetBound l * (D0 * epsilon) := by
                apply Finset.sum_le_sum
                intro l _
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (centeredCylinderChristoffel_jet_bound l b i c)
                    (Nat.cast_nonneg _)
                · exact hlow (j - l) (Nat.sub_le _ _) a
                · exact norm_nonneg _
                · exact mul_nonneg (Nat.cast_nonneg _)
                    (centeredCylinderChristoffelJetBound_pos l).le
              _ = S * epsilon := by simp only [S, Finset.sum_mul, mul_assoc]
          have hdirection (i : Fin 3) :
              ‖iteratedFDeriv ℝ j (fun p =>
                fderiv ℝ (centeredCylinderComponent B z.1 z.2 k a) p
                  (EuclideanSpace.basisFun (Fin 3) ℝ i)) 0‖ ≤
                (A + 3 * (2 + (k : ℝ)) * S) * epsilon := by
            let H (l : Fin (2 + k)) (b : Fin 3) (p : E₃) :=
              centeredCylinderChristoffel b i (a l) p *
                centeredCylinderComponent B z.1 z.2 k (Function.update a l b) p
            have hH (l : Fin (2 + k)) (b : Fin 3) : ContDiffAt ℝ ∞ (H l b) 0 :=
              (centeredCylinderChristoffel_contDiff b i (a l)).contDiffAt.mul (hcomponent k _)
            have hsumSmooth : ContDiffAt ℝ ∞ (fun p => ∑ l, ∑ b, H l b p) 0 :=
              ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun b _ => hH l b))
            have hsum : ‖iteratedFDeriv ℝ j (fun p => ∑ l, ∑ b, H l b p) 0‖ ≤
                3 * (2 + (k : ℝ)) * S * epsilon := by
              calc
                _ ≤ ∑ l : Fin (2 + k),
                    ‖iteratedFDeriv ℝ j (fun p => ∑ b, H l b p) 0‖ :=
                  norm_iteratedFDeriv_finite_sum _
                    (fun l => ContDiffAt.sum (fun b _ => hH l b)) j
                _ ≤ ∑ l : Fin (2 + k), ∑ b : Fin 3,
                    ‖iteratedFDeriv ℝ j (H l b) 0‖ :=
                  Finset.sum_le_sum (fun l _ => norm_iteratedFDeriv_finite_sum _ (hH l) j)
                _ ≤ ∑ _l : Fin (2 + k), ∑ _b : Fin 3, S * epsilon :=
                  Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun b _ =>
                    hproduct i b (a l) (Function.update a l b)))
                _ = _ := by simp; ring
            have heq : (fun p => fderiv ℝ (centeredCylinderComponent B z.1 z.2 k a) p
                (EuclideanSpace.basisFun (Fin 3) ℝ i)) =
                fun p => centeredCylinderComponent B z.1 z.2 (k + 1) (Fin.cons i a) p +
                  ∑ l, ∑ b, H l b p :=
              funext (centeredCylinderComponent_fderiv_basis B z.1 z.2 k a i)
            rw [heq, fun_iteratedFDeriv_add_apply
              ((hcomponent (k + 1) _).of_le (by exact_mod_cast le_top))
              (hsumSmooth.of_le (by exact_mod_cast le_top))]
            calc
              _ ≤ ‖iteratedFDeriv ℝ j
                  (centeredCylinderComponent B z.1 z.2 (k + 1) (Fin.cons i a)) 0‖ +
                  ‖iteratedFDeriv ℝ j (fun p => ∑ l, ∑ b, H l b p) 0‖ := norm_add_le _ _
              _ ≤ A * epsilon + 3 * (2 + (k : ℝ)) * S * epsilon :=
                add_le_add (hAbound hepsilon hB (by omega) z hz _) hsum
              _ = _ := by ring
          calc
            _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ j (fun p =>
                fderiv ℝ (centeredCylinderComponent B z.1 z.2 k a) p
                  (EuclideanSpace.basisFun (Fin 3) ℝ i)) 0‖ :=
              norm_iteratedFDeriv_succ_le_basis (hcomponent k a) j
            _ ≤ ∑ _i : Fin 3, (A + 3 * (2 + (k : ℝ)) * S) * epsilon :=
              Finset.sum_le_sum (fun i _ => hdirection i)
            _ = _ := by simp; ring



theorem exists_centeredCylinderError_jet_bound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {epsilon : ℝ}, 0 < epsilon →
      ∀ {B : RoundCylinderTwoTensor}, RoundCylinderClose epsilon 0 B →
      m ≤ ⌊epsilon⁻¹⌋₊ →
      ∀ z : RoundCylinderSpace,
        z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
          ‖iteratedFDeriv ℝ m (centeredCylinderError B z.1 z.2) 0‖ ≤ C * epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_centeredCylinderComponent_jet_bound m 0
  refine ⟨9 * C, by positivity, ?_⟩
  intro epsilon hepsilon B hB horder z hz
  let V (i j : Fin 3) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ i)).smulRight
      (innerSL ℝ (EuclideanSpace.basisFun (Fin 3) ℝ j))
  have hV (i j : Fin 3) : ‖V i j‖ = 1 := by
    simp [V]
  let H (i j : Fin 3) (p : E₃) :=
    centeredCylinderComponent B z.1 z.2 0 ![i, j] p • V i j
  have hH (i j : Fin 3) : ContDiffAt ℝ ∞ (H i j) 0 :=
    (centeredCylinderComponent_contDiffAt hB z hz 0 ![i, j]).smul contDiffAt_const
  have hterm (i j : Fin 3) : ‖iteratedFDeriv ℝ m (H i j) 0‖ ≤ C * epsilon := by
    have h := norm_iteratedFDeriv_smul_fixed
      (centeredCylinderComponent_contDiffAt hB z hz 0 ![i, j]) (V i j) m
    rw [hV, mul_one] at h
    exact h.trans (hbound hepsilon hB (by simpa using horder) z hz _)
  have heq : centeredCylinderError B z.1 z.2 = fun p => ∑ i, ∑ j, H i j p := rfl
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ m (fun p => ∑ j, H i j p) 0‖ :=
      norm_iteratedFDeriv_finite_sum _ (fun i => ContDiffAt.sum (fun j _ => hH i j)) m
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖iteratedFDeriv ℝ m (H i j) 0‖ :=
      Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_finite_sum _ (hH i) m)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C * epsilon :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp; ring

end PoincareConjecture.MetricSurgery
