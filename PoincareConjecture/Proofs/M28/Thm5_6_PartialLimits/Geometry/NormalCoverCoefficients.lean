import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverCharts
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPrecompose
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, ℝ → RiemannianMetric n (M k)} {p : ∀ k, M k}
    {T' T : ℝ} {r R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover (g k) (p k)
      T' T (r j) (R j) (ρ j) (a j) (b j) (N j))

local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩



theorem partialUnitBallMap_eventually_lower_coefficients
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (ha : ∀ j, 0 < a j)
    (i : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ t ∈ Ioo T' T,
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ (g k t).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (partialUnitBallMap cover k i)) x v v := by
  let j := (Nat.unpair i).1
  refine ⟨a j * (ρ j / 2) ^ 2,
    mul_pos (ha j) (sq_pos_of_pos (half_pos (hρ j))), ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk t ht x hx v
  rw [partialUnitBallMap_of_le cover k i hk]
  exact (cover k j hk).unitBallMap_lower_coefficients (hρ j) (hρR j) _ ht hx v



theorem partialUnitBallMap_eventually_bounded_derivatives
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    (hraw : ∀ j m, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ hjk : j ≤ k,
      (cover k j hjk).HasMetricJetBound m B) (i : ℕ) :
    LocallyEventuallyBoundedDerivatives (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (fun k => (g k 0).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (partialUnitBallMap cover k i))) := by
  let j := (Nat.unpair i).1
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ρ j / 2) • ContinuousLinearMap.id ℝ _
  let rawStage := fun k j (hjk : j ≤ k) =>
    (g k 0).pullbackCoefficients ((cover k j hjk).chart
      ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
  let raw := fun k => rawStage k (min j k) (min_le_right _ _)
  have hstage (k : ℕ) (hk : j ≤ k) : raw k = rawStage k j hk := by
    funext x
    simp only [raw, min_eq_left hk]
  have heq (k : ℕ) (hk : j ≤ k) : EqOn
      ((g k 0).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (partialUnitBallMap cover k i)))
      (fun x => (ρ j / 2) ^ 2 • raw k (L x)) (ball 0 1) := by
    intro x hx
    rw [partialUnitBallMap_of_le cover k i hk, hstage k hk]
    ext v w
    exact (cover k j hk).unitBallMap_pullbackCoefficients (hρ j) (hρR j) _ 0 hx v w
  have hsmooth (k : ℕ) (hk : j ≤ k) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ ball 0 1) : ContDiffAt ℝ ∞ (raw k) (L x) := by
    rw [hstage k hk]
    apply (g k 0).contDiffAt_pullbackCoefficients
    apply (cover k j hk).chart _ |>.contMDiffOn.contMDiffAt
    apply (cover k j hk).chart _ |>.open_source.mem_nhds
    rw [(cover k j hk).source]
    exact (ball_subset_ball (hρR j))
      (NormalChartCover.rescale_mem_half_ball (hρ j) ⟨x, hx⟩)
  intro K _hK hKU m
  obtain ⟨B, hB⟩ := hraw j m
  refine ⟨‖(ρ j / 2) ^ 2‖ * (B * ∏ _ : Fin m, ‖L‖), ?_⟩
  filter_upwards [hB, eventually_ge_atTop j] with k hkB hk x hx
  rw [eqOn_iteratedFDeriv_of_isOpen isOpen_ball (heq k hk) m (hKU hx)]
  have hcomp : ContDiffAt ℝ ∞ (raw k ∘ L) x :=
    (hsmooth k hk x (hKU hx)).comp x L.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ m (fun x => (ρ j / 2) ^ 2 • (raw k ∘ L) x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (i := m) (a := (ρ j / 2) ^ 2)
    (hcomp.of_le (by exact_mod_cast le_top))]
  let : IsBoundedSMul ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
    (hsmooth k hk x (hKU hx)) m]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply ((iteratedFDeriv ℝ m (raw k) (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  rw [hstage k hk]
  apply hkB hk
  exact (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (half_le_self (hρ j).le)))
      (NormalChartCover.rescale_mem_half_ball (hρ j) ⟨x, hKU hx⟩)

end PoincareConjecture.M28
