import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


def testFunctions (U : Set (M × ℝ)) : Submodule ℝ (M × ℝ → ℝ) where
  carrier := {φ | ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ ∧
    HasCompactSupport φ ∧ tsupport φ ⊆ U}
  zero_mem' := ⟨contMDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
      (tsupport_add (f := φ) (g := ψ)).trans (union_subset hφ.2.2 hψ.2.2)⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨contMDiff_const.mul hφ.1, hφ.2.1.smul_left,
      (closure_mono (Function.support_const_smul_subset c φ)).trans hφ.2.2⟩

instance {U : Set (M × ℝ)} : CoeFun (testFunctions (n := n) U)
    (fun _ => M × ℝ → ℝ) := ⟨fun φ => φ.val⟩

theorem test_smooth_space {U : Set (M × ℝ)} (φ : testFunctions (n := n) U) (τ : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ (x, τ)) :=
  φ.property.1.comp (contMDiff_id.prodMk contMDiff_const)

theorem test_smooth_time {U : Set (M × ℝ)} (φ : testFunctions (n := n) U) (x : M) :
    ContDiff ℝ ∞ (fun τ => φ (x, τ)) :=
  (φ.property.1.comp (contMDiff_const.prodMk contMDiff_id)).contDiff


def testOperator (F : RicciFlow n M J) (φ : M × ℝ → ℝ) (z : M × ℝ) : ℝ :=
  deriv (fun τ => φ (z.1, τ)) z.2 +
    (F.connection (-z.2)).laplacian (fun x => φ (x, z.2)) z.1

theorem testOperator_add (F : RicciFlow n M J) {U : Set (M × ℝ)}
    (φ ψ : testFunctions (n := n) U) :
    testOperator F ((φ + ψ : testFunctions (n := n) U) : M × ℝ → ℝ) =
      testOperator F φ + testOperator F ψ := by
  funext z
  change deriv (fun τ => φ (z.1, τ) + ψ (z.1, τ)) z.2 +
    (F.connection (-z.2)).laplacian (fun x => φ (x, z.2) + ψ (x, z.2)) z.1 = _
  rw [deriv_fun_add ((test_smooth_time φ z.1).differentiable (by simp) z.2)
    ((test_smooth_time ψ z.1).differentiable (by simp) z.2),
    (F.connection (-z.2)).laplacian_add (test_smooth_space φ z.2)
      (test_smooth_space ψ z.2)]
  simp only [testOperator, Pi.add_apply]
  ring

theorem testOperator_smul (F : RicciFlow n M J) {U : Set (M × ℝ)}
    (c : ℝ) (φ : testFunctions (n := n) U) :
    testOperator F ((c • φ : testFunctions (n := n) U) : M × ℝ → ℝ) =
      c • testOperator F φ := by
  funext z
  change deriv (fun τ => c * φ (z.1, τ)) z.2 +
    (F.connection (-z.2)).laplacian (fun x => c * φ (x, z.2)) z.1 = _
  rw [deriv_const_mul c ((test_smooth_time φ z.1).differentiable (by simp) z.2),
    (F.connection (-z.2)).laplacian_const_mul]
  simp only [testOperator, Pi.smul_apply, smul_eq_mul, mul_add]


def testOperatorLinear (F : RicciFlow n M J) (U : Set (M × ℝ)) :
    testFunctions (n := n) U →ₗ[ℝ] (M × ℝ → ℝ) where
  toFun φ := testOperator F φ
  map_add' := testOperator_add F
  map_smul' := testOperator_smul F

section Pairing

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

def weakPairing (F : RicciFlow n M J) (u φ : M × ℝ → ℝ) : ℝ :=
  ∫ τ, ∫ x, u (x, τ) * testOperator F φ (x, τ) ∂(F.metric (-τ)).volumeMeasure


def weakPairingLinear (F : RicciFlow n M J) (u : M × ℝ → ℝ)
    (U : Set (M × ℝ))
    (hspace : ∀ φ : testFunctions (n := n) U, ∀ τ,
      Integrable (fun x => u (x, τ) * testOperator F φ (x, τ))
        (F.metric (-τ)).volumeMeasure)
    (htime : ∀ φ : testFunctions (n := n) U,
      Integrable (fun τ => ∫ x, u (x, τ) * testOperator F φ (x, τ)
        ∂(F.metric (-τ)).volumeMeasure)) :
    testFunctions (n := n) U →ₗ[ℝ] ℝ where
  toFun φ := weakPairing F u φ
  map_add' φ ψ := by
    simp only [weakPairing, testOperator_add, Pi.add_apply, mul_add,
      integral_add (hspace φ _) (hspace ψ _), integral_add (htime φ) (htime ψ)]
  map_smul' c φ := by
    simp only [weakPairing, testOperator_smul, Pi.smul_apply, smul_eq_mul,
      mul_left_comm (u _), integral_const_mul]
    rfl

end Pairing


theorem abs_apply_le_test_cutoff {U : Set (M × ℝ)}
    (T : testFunctions (n := n) U →ₗ[ℝ] ℝ)
    (hT : ∀ ψ : testFunctions (n := n) U, (∀ z, 0 ≤ ψ z) → 0 ≤ T ψ)
    (χ φ : testFunctions (n := n) U) (hχ : ∀ z, 0 ≤ χ z)
    (hone : ∀ z ∈ tsupport (φ : M × ℝ → ℝ), χ z = 1)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ z, |φ z| ≤ B) :
    |T φ| ≤ B * T χ := by
  have hbound (z : M × ℝ) : |φ z| ≤ B * χ z := by
    by_cases hz : z ∈ tsupport (φ : M × ℝ → ℝ)
    · simpa only [hone z hz, mul_one] using hφB z
    · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
      exact mul_nonneg hB (hχ z)
  have hm := hT (B • χ - φ) (fun z => by
    change 0 ≤ B * χ z - φ z
    exact sub_nonneg.mpr ((le_abs_self _).trans (hbound z)))
  have hp := hT (B • χ + φ) (fun z => by
    change 0 ≤ B * χ z + φ z
    have := (neg_le_abs (φ z)).trans (hbound z)
    linarith)
  simp only [map_sub, map_add, map_smul, smul_eq_mul] at hm hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩


theorem apply_eq_zero_of_test_cutoffs {U : Set (M × ℝ)}
    (T : testFunctions (n := n) U →ₗ[ℝ] ℝ)
    (hT : ∀ ψ : testFunctions (n := n) U, (∀ z, 0 ≤ ψ z) → 0 ≤ T ψ)
    (φ : testFunctions (n := n) U)
    (χ : ℕ → testFunctions (n := n) U) (hχ : ∀ j z, 0 ≤ χ j z)
    (hone : ∀ᶠ j in atTop, ∀ z ∈ tsupport (φ : M × ℝ → ℝ), χ j z = 1)
    (hmass : Tendsto (fun j => T (χ j)) atTop (𝓝 0)) : T φ = 0 := by
  obtain ⟨B, hB⟩ := φ.property.1.continuous.bounded_above_of_compact_support φ.property.2.1
  have hbound : ∀ᶠ j in atTop, |T φ| ≤ max B 0 * T (χ j) := by
    filter_upwards [hone] with j hj
    exact abs_apply_le_test_cutoff T hT (χ j) φ (hχ j) hj (le_max_right _ _)
      (fun z => by
        have hb : |φ z| ≤ B := by simpa only [Real.norm_eq_abs] using hB z
        exact hb.trans (le_max_left _ _))
  have hz : |T φ| ≤ 0 := by
    simpa only [mul_zero] using ge_of_tendsto (tendsto_const_nhds.mul hmass) hbound
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

end PoincareConjecture.RicciFlow.ConjugateHeat
