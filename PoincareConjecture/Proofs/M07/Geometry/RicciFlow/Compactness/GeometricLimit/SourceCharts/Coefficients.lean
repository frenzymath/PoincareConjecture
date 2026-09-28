import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric Poincare.Gluing
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {p : M} {T' T A R ρ a b : ℝ} {N : ℕ}

local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩



theorem unitBallMap_pullbackCoefficients
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1)) (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 1)
    (v w : EuclideanSpace ℝ (Fin n)) :
    (g t).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)) x v w =
      (ρ / 2) ^ 2 * (g t).pullbackCoefficients (C.chart i) ((ρ / 2) • x) v w := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ρ / 2) • ContinuousLinearMap.id ℝ _
  let f := ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
    (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)
  have heq : (C.chart i) ∘ L =ᶠ[𝓝 x] f := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    change C.chart i ((ρ / 2) • y) = f (⟨y, hy⟩ : ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    exact (ChartDistance.chartParametrization_apply (fun _ : ℕ => ball 0 1)
      (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i) ⟨y, hy⟩).symm
  have hxsource : L x ∈ (C.chart i).source := by
    rw [C.source]
    exact (ball_subset_ball hρR) (rescale_mem_half_ball hρ ⟨x, hx⟩)
  have he := ((C.chart i).contMDiffOn.contMDiffAt
    ((C.chart i).open_source.mem_nhds hxsource)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x he L.differentiableAt.mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv] at hd
  change (g t).inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x w) =
    (ρ / 2) ^ 2 * (g t).inner (C.chart i (L x))
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) (L x) v)
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) (L x) w)
  rw [hd]
  have hpoint := heq.self_of_nhds
  change C.chart i (L x) = f x at hpoint
  rw [← hpoint]
  simp only [ContinuousLinearMap.comp_apply, L, smul_apply, map_smul, smul_eq_mul]
  change (ρ / 2) * ((ρ / 2) * (g t).inner (C.chart i ((ρ / 2) • x))
    (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) v)
    (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) w)) =
    (ρ / 2) ^ 2 * (g t).inner (C.chart i ((ρ / 2) • x))
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) v)
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) w)
  ring



theorem unitBallMap_lower_coefficients
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    {t : ℝ} (ht : t ∈ Ioo T' T) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    (a * (ρ / 2) ^ 2) * ‖v‖ ^ 2 ≤
      (g t).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)) x v v := by
  rw [unitBallMap_pullbackCoefficients C hρ hρR i t hx]
  have hx' : (ρ / 2) • x ∈ closedBall 0 (2 * ρ) :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (rescale_mem_half_ball hρ ⟨x, hx⟩)
  have h := mul_le_mul_of_nonneg_left (C.coefficients i t ht _ hx' v).1 (sq_nonneg (ρ / 2))
  nlinarith only [h]

section Sequence

variable {S : PointedFlowSequence n T' T}

local instance (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance (k : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold

variable {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))



theorem diagonalUnitBallMap_eventually_lower_coefficients
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (ha : ∀ j, 0 < a j)
    (i : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ t ∈ Ioo T' T,
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (diagonalUnitBallMap cover k i)) x v v := by
  let j := (Nat.unpair i).1
  refine ⟨a j * (ρ j / 2) ^ 2,
    mul_pos (ha j) (sq_pos_of_pos (half_pos (hρ j))), ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk t ht x hx v
  rw [diagonalUnitBallMap_of_le cover k i hk]
  exact unitBallMap_lower_coefficients (cover k j hk) (hρ j) (hρR j) _ ht hx v

end Sequence

end PoincareConjecture.NormalChartCover
