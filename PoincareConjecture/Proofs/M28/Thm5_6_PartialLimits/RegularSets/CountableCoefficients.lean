import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CountableCharts
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CurvatureJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Coefficients
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPrecompose
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.M28.RegularNormalChartCover

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {p : M} {δ R ρ : ℝ} {N : ℕ}

local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩



theorem unitBallMap_pullbackCoefficients
    (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 1)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)) x v w =
      (ρ / 2) ^ 2 * g.pullbackCoefficients (C.chart i) ((ρ / 2) • x) v w := by
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
    exact (ball_subset_ball hρR) (NormalChartCover.rescale_mem_half_ball hρ ⟨x, hx⟩)
  have he := ((C.chart i).contMDiffOn.contMDiffAt
    ((C.chart i).open_source.mem_nhds hxsource)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x he L.differentiableAt.mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv, L.fderiv] at hd
  change g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x w) =
    (ρ / 2) ^ 2 * g.inner (C.chart i (L x))
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) (L x) v)
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) (L x) w)
  rw [hd]
  have hpoint := heq.self_of_nhds
  change C.chart i (L x) = f x at hpoint
  rw [← hpoint]
  simp only [ContinuousLinearMap.comp_apply, L, smul_apply, map_smul, smul_eq_mul]
  change (ρ / 2) * ((ρ / 2) * g.inner (C.chart i ((ρ / 2) • x))
    (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) v)
    (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) w)) =
    (ρ / 2) ^ 2 * g.inner (C.chart i ((ρ / 2) • x))
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) v)
      (mfderiv (𝓡 n) (𝓡 n) (C.chart i) ((ρ / 2) • x) w)
  ring



theorem unitBallMap_lower_coefficients
    (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    ((1 / 4 : ℝ) * (ρ / 2) ^ 2) * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)) x v v := by
  rw [unitBallMap_pullbackCoefficients C hρ hρR i hx]
  have hx' : (ρ / 2) • x ∈ closedBall 0 (2 * ρ) :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
      (NormalChartCover.rescale_mem_half_ball hρ ⟨x, hx⟩)
  have h := mul_le_mul_of_nonneg_left (C.coefficients i _ hx' v).1 (sq_nonneg (ρ / 2))
  nlinarith only [h]

end PoincareConjecture.M28.RegularNormalChartCover

namespace PoincareConjecture.M28

variable {n : ℕ} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k}
    {δ R ρ : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → RegularNormalChartCover (g k) (p k)
      (δ j) (R j) (ρ j) (N j))

local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩



theorem regularUnitBallMap_eventually_lower_coefficients
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (i : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ (g k).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover k i)) x v v := by
  let j := (Nat.unpair i).1
  refine ⟨(1 / 4 : ℝ) * (ρ j / 2) ^ 2,
    mul_pos (by norm_num) (sq_pos_of_pos (half_pos (hρ j))), ?_⟩
  filter_upwards [eventually_ge_atTop j] with k hk x hx v
  rw [regularUnitBallMap_of_le cover k i hk]
  exact (cover k j hk).unitBallMap_lower_coefficients (hρ j) (hρR j) _ hx v



theorem regularUnitBallMap_eventually_bounded_derivatives
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j)
    (hraw : ∀ j m, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ hjk : j ≤ k,
      ∀ l : Fin (N j + 1), ∀ x ∈ closedBall 0 (ρ j),
        ‖iteratedFDeriv ℝ m ((g k).pullbackCoefficients ((cover k j hjk).chart l)) x‖ ≤ B)
    (i : ℕ) :
    LocallyEventuallyBoundedDerivatives (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (fun k => (g k).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover k i))) := by
  let j := (Nat.unpair i).1
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ρ j / 2) • ContinuousLinearMap.id ℝ _
  let rawStage := fun k j (hjk : j ≤ k) =>
    (g k).pullbackCoefficients ((cover k j hjk).chart
      ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
  let raw := fun k => rawStage k (min j k) (min_le_right _ _)
  have hstage (k : ℕ) (hk : j ≤ k) : raw k = rawStage k j hk := by
    funext x
    simp only [raw, min_eq_left hk]
  have heq (k : ℕ) (hk : j ≤ k) : EqOn
      ((g k).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover k i)))
      (fun x => (ρ j / 2) ^ 2 • raw k (L x)) (ball 0 1) := by
    intro x hx
    rw [regularUnitBallMap_of_le cover k i hk, hstage k hk]
    ext v w
    exact (cover k j hk).unitBallMap_pullbackCoefficients (hρ j) (hρR j) _ hx v w
  have hsmooth (k : ℕ) (hk : j ≤ k) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ ball 0 1) : ContDiffAt ℝ ∞ (raw k) (L x) := by
    rw [hstage k hk]
    apply (g k).contDiffAt_pullbackCoefficients
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




theorem regularUnitBallMap_bounded_derivatives_of_curvature
    (D : ∀ k, LeviCivitaData (g k))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j < R j)
    (hcurv : ∀ j l, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ x ∈ regularComponent (g k) (p k) (2 * δ j),
        (D k).curvatureDerivativeNorm l x ≤ C) (i : ℕ) :
    LocallyEventuallyBoundedDerivatives (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (fun k => (g k).pullbackCoefficients
        (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (regularUnitBallMap cover k i))) := by
  apply regularUnitBallMap_eventually_bounded_derivatives cover hρ
    (fun j => (half_le_self (hρ j).le).trans (hρR j).le) ?_ i
  intro j m
  obtain ⟨B, _, hB⟩ := eventually_regular_normalCover_jet_bound_of_curvature
    D (hρ j) (hρR j) (hcurv j) m
  exact ⟨B, hB.mono fun k hk hjk => hk (cover k j hjk)⟩

end PoincareConjecture.M28
