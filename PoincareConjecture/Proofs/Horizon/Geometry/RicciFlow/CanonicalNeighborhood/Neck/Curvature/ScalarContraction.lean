import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.JetEstimates
import PoincareConjecture.Proofs.M34.Standard.ScalarJetOperator

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12

open scoped BigOperators

namespace PoincareConjecture.EpsilonNeck

open SpacetimeBounds

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |a - c| * |d| := by
  calc
    _ = |a * (b - d) + (a - c) * d| := by congr 1; ring
    _ ≤ |a * (b - d)| + |(a - c) * d| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

private theorem abs_sum_three_three_le {f : Fin 3 → Fin 3 → ℝ} {C : ℝ}
    (h : ∀ i j, |f i j| ≤ C) : |∑ i, ∑ j, f i j| ≤ 9 * C := by
  calc
    _ ≤ ∑ i, ∑ j, |f i j| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by simp; ring

private theorem norm_euclidean_proj_le (i : Fin 3) :
    ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa using PiLp.norm_apply_le v i

private theorem abs_inverse_component_le
    (I : (EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    {C : ℝ} (hI : ‖I‖ ≤ C) (i j : Fin 3) :
    |EuclideanSpace.proj j (I (EuclideanSpace.proj i))| ≤ C := by
  have hC := (norm_nonneg _).trans hI
  calc
    _ ≤ ‖I (EuclideanSpace.proj i)‖ := PiLp.norm_apply_le _ j
    _ ≤ ‖I‖ * ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ := I.le_opNorm _
    _ ≤ C * 1 := mul_le_mul hI (norm_euclidean_proj_le i) (norm_nonneg _) hC
    _ = C := mul_one _

theorem scalarTwoJet_sub_le {J J₀ : MetricTwoJet 3} {δ K : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ‖J.1‖ ≤ 3) (hi : ‖J.1.inverse‖ ≤ 2)
    (hi₀ : ‖J₀.1.inverse‖ ≤ 1) (hdi : ‖J.1.inverse - J₀.1.inverse‖ ≤ 2 * δ)
    (hfirst : ‖J.2.1‖ ≤ δ) (hfirst₀ : J₀.2.1 = 0)
    (hsecond : ‖J.2.2 - J₀.2.2‖ ≤ δ) (hsecond₀ : ‖J₀.2.2‖ ≤ K) :
    |M34.scalarTwoJet J - M34.scalarTwoJet J₀| ≤ (20088 + 972 * K) * δ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hsecond₀
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hb (i : Fin 3) : ‖b i‖ ≤ 1 := by simp [b]
  let I := fun (J : MetricTwoJet 3) (i j : Fin 3) =>
    EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i))
  have hI (i j : Fin 3) : |I J i j| ≤ 2 := abs_inverse_component_le _ hi i j
  have hI₀ (i j : Fin 3) : |I J₀ i j| ≤ 1 := abs_inverse_component_le _ hi₀ i j
  have hdI (i j : Fin 3) : |I J i j - I J₀ i j| ≤ 2 * δ := by
    simpa only [I, sub_apply, map_sub] using
      abs_inverse_component_le _ hdi i j
  have hR (i j k l : Fin 3) :
      |jetCurvature J (b i) (b k) (b j) (b l) -
        jetCurvature J₀ (b i) (b k) (b j) (b l)| ≤ 62 * δ :=
    jetCurvature_sub_le hδ hδone hg hi hfirst hfirst₀ hsecond _ _ _ _
      (hb i) (hb k) (hb j) (hb l)
  have hR₀ (i j k l : Fin 3) : |jetCurvature J₀ (b i) (b k) (b j) (b l)| ≤ 2 * K :=
    jetCurvature_le_of_first_zero hfirst₀ hsecond₀ _ _ _ _ (hb i) (hb k) (hb j) (hb l)
  have hRic (i j : Fin 3) : |jetRicci J (b i) (b j) - jetRicci J₀ (b i) (b j)| ≤
      (1116 + 36 * K) * δ := by
    simp only [jetRicci, ← Finset.sum_sub_distrib]
    apply (abs_sum_three_three_le (C := (124 + 4 * K) * δ) ?_).trans_eq (by ring)
    intro k l
    calc
        _ ≤ |I J k l| * |jetCurvature J (b i) (b k) (b j) (b l) -
            jetCurvature J₀ (b i) (b k) (b j) (b l)| +
            |I J k l - I J₀ k l| * |jetCurvature J₀ (b i) (b k) (b j) (b l)| :=
          abs_mul_sub_mul_le _ _ _ _
        _ ≤ 2 * (62 * δ) + (2 * δ) * (2 * K) := by
          gcongr
          exact hI k l
          exact hR i j k l
          exact hdI k l
          exact hR₀ i j k l
        _ = _ := by ring
  have hRic₀ (i j : Fin 3) : |jetRicci J₀ (b i) (b j)| ≤ 18 * K := by
    apply (abs_sum_three_three_le (C := 2 * K) ?_).trans_eq (by ring)
    intro k l
    rw [abs_mul]
    exact (mul_le_mul (hI₀ k l) (hR₀ i j k l) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  simp only [M34.scalarTwoJet, ← Finset.sum_sub_distrib]
  apply (abs_sum_three_three_le (C := (2232 + 108 * K) * δ) ?_).trans_eq (by ring)
  intro i j
  calc
      _ ≤ |I J i j| * |jetRicci J (b i) (b j) - jetRicci J₀ (b i) (b j)| +
          |I J i j - I J₀ i j| * |jetRicci J₀ (b i) (b j)| := abs_mul_sub_mul_le _ _ _ _
      _ ≤ 2 * ((1116 + 36 * K) * δ) + (2 * δ) * (18 * K) := by
        gcongr
        exact hI i j
        exact hRic i j
        exact hdI i j
        exact hRic₀ i j
      _ = _ := by ring

end PoincareConjecture.EpsilonNeck
