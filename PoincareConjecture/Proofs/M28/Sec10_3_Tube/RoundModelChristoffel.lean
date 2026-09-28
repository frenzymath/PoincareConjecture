import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundModelMetricJets
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundNormalJetConversion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Connection.JetBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussMetricExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

open PoincareConjecture.CoordinateExponential
open PoincareConjecture.SpacetimeBounds

theorem exists_round_model_christoffel_jet_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : EuclideanSpace ℝ (Fin 3) → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (hcenter : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ j ≤ 1, ∀ u v : EuclideanSpace ℝ (Fin 3),
        ‖iteratedFDeriv ℝ j (fun y => christoffelBilinear
          (N.model_metric.pullbackCoefficients e) y u v) 0‖ ≤
          C * ‖u‖ * ‖v‖ := by
  have hR : 0 < R := hρ.trans hρR
  obtain ⟨B₁, hB₁, hjet₁⟩ :=
    exists_round_model_pullback_metric_jet_bound N 1 hρ hρR e he hi hcenter hgauss
  obtain ⟨B₂, hB₂, hjet₂⟩ :=
    exists_round_model_pullback_metric_jet_bound N 2 hρ hρR e he hi hcenter hgauss
  let B := N.model_metric.pullbackCoefficients e
  have hBcont : ContDiffAt ℝ ∞ B 0 := by
    exact N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR)))
  have hBnorm : ‖B 0‖ ≤ 1 := by
    have hEq : B 0 = innerSL ℝ := by
      ext v w
      exact hcenter v w
    rw [hEq]
    exact norm_innerSL_le ℝ
  have hBell : ∀ v : EuclideanSpace ℝ (Fin 3),
      1 * ‖v‖ ^ 2 ≤ B 0 v v := by
    intro v
    rw [hcenter]
    simp only [real_inner_self_eq_norm_sq, one_mul]
    exact le_refl _
  let D : ℝ := max 1 (max B₁ B₂)
  have hD1 : 1 ≤ D := by
    exact le_max_left 1 (max B₁ B₂)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  have hjet (j : ℕ) (hj₁ : 1 ≤ j) (hj₂ : j ≤ 2) :
      ‖iteratedFDeriv ℝ j B 0‖ ≤ D ^ j := by
    have hj : j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl
    · have h := hjet₁ 0 (by simp [hρ.le])
      calc
        ‖iteratedFDeriv ℝ 1 B 0‖ ≤ B₁ := h
        _ ≤ D := le_trans (le_max_left B₁ B₂) (le_max_right 1 (max B₁ B₂))
        _ = D ^ 1 := by simp
    · have h := hjet₂ 0 (by simp [hρ.le])
      have hB₂D : B₂ ≤ D :=
        le_trans (le_max_right B₁ B₂) (le_max_right 1 (max B₁ B₂))
      have hDD : D ≤ D ^ 2 := by
        simp only [pow_two]
        nlinarith
      exact h.trans (hB₂D.trans hDD)
  obtain ⟨C, hC, hchrist⟩ :=
    exists_uniform_christoffel_jet_bound
      (E := EuclideanSpace ℝ (Fin 3)) 1 (a := (1 : ℝ)) (by norm_num)
        1 D hD1
  refine ⟨C, hC, ?_⟩
  intro j hj u v
  exact hchrist B 0 hBcont hBnorm hBell hjet j hj u v

theorem exists_round_model_christoffel_operator_jet_bound
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : EuclideanSpace ℝ (Fin 3) → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (h0 : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ u v : EuclideanSpace ℝ (Fin 3),
        ‖(fderiv ℝ (christoffelBilinear
          (N.model_metric.pullbackCoefficients e)) 0 u) v‖ ≤
          C * ‖u‖ * ‖v‖) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (christoffelBilinear
          (N.model_metric.pullbackCoefficients e)) 0 u‖ ≤ C * ‖u‖) ∧
      ‖fderiv ℝ (christoffelBilinear
        (N.model_metric.pullbackCoefficients e)) 0‖ ≤ C := by
  obtain ⟨C, hC, hcomp⟩ :=
    exists_round_model_christoffel_jet_bound N hρ hρR e he hi h0 hgauss
  let B := N.model_metric.pullbackCoefficients e
  have hR : 0 < R := hρ.trans hρR
  have hBcont : ContDiffAt ℝ ∞ B 0 := by
    exact N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR)))
  have hBinv : (B 0).IsInvertible := by
    exact N.model_metric.isInvertible_pullbackCoefficients
      (hi 0 (mem_ball.mpr (by simpa using hR))).injective
  have hΓd : DifferentiableAt ℝ (christoffelBilinear B) 0 :=
    (contDiffAt_christoffelBilinear hBcont hBinv).differentiableAt (by simp)
  have hderiv (v w : EuclideanSpace ℝ (Fin 3)) :
      ‖fderiv ℝ (fun y => (christoffelBilinear B y) v w) 0‖ ≤
        C * ‖v‖ * ‖w‖ := by
    simpa only [norm_iteratedFDeriv_one] using hcomp 1 le_rfl v w
  have hpoint (u v w : EuclideanSpace ℝ (Fin 3)) :
      ‖(fderiv ℝ (christoffelBilinear B) 0 u) v w‖ ≤
        C * ‖u‖ * ‖v‖ * ‖w‖ := by
    have h := hderiv v w
    have hu := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (fun y => (christoffelBilinear B y) v w) 0) u
    have heq : fderiv ℝ (fun y => (christoffelBilinear B y) v w) 0 u =
        (fderiv ℝ (christoffelBilinear B) 0 u) v w := by
      rw [fderiv_clm_apply
        (hΓd.clm_apply (differentiableAt_const (c := v)))
        (differentiableAt_const (c := w)),
        fderiv_clm_apply hΓd (differentiableAt_const (c := v))]
      simp
    rw [← heq]
    calc
      ‖fderiv ℝ (fun y => (christoffelBilinear B y) v w) 0 u‖ ≤
          ‖fderiv ℝ (fun y => (christoffelBilinear B y) v w) 0‖ * ‖u‖ := hu
      _ ≤ (C * ‖v‖ * ‖w‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg u)
      _ = C * ‖u‖ * ‖v‖ * ‖w‖ := by ring
  have happ (u v : EuclideanSpace ℝ (Fin 3)) :
      ‖(fderiv ℝ (christoffelBilinear B) 0 u) v‖ ≤
        C * ‖u‖ * ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _
    · positivity
    intro w
    exact hpoint u v w |>.trans_eq (by ring)
  have hop (u : EuclideanSpace ℝ (Fin 3)) :
      ‖fderiv ℝ (christoffelBilinear B) 0 u‖ ≤ C * ‖u‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _
    · positivity
    intro v
    exact happ u v
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro u v
    exact happ u v
  · intro u
    exact hop u
  · apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    exact hop u

theorem round_model_christoffel_zero
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (e : EuclideanSpace ℝ (Fin 3) → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R))
    (hi : ∀ x ∈ ball 0 R,
      (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible)
    (_h0 : ∀ v w,
      N.model_metric.pullbackCoefficients e 0 v w = inner ℝ v w)
    (hgauss : ∀ x ∈ ball 0 R, ∀ w,
      N.model_metric.pullbackCoefficients e x x w = inner ℝ x w) :
    christoffelBilinear (N.model_metric.pullbackCoefficients e) 0 = 0 := by
  have hR : 0 < R := hρ.trans hρR
  let B := N.model_metric.pullbackCoefficients e
  have hB : ContDiffOn ℝ ∞ B (ball 0 R) := by
    intro x hx
    exact (N.model_metric.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds hx))).contDiffWithinAt
  have hsymm : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      ∀ v w, B x v w = B x w v := by
    intro x hx v w
    change N.model_metric.inner (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v)
      (mfderiv (𝓡 3) (𝓡 3) e x w) =
      N.model_metric.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x w)
        (mfderiv (𝓡 3) (𝓡 3) e x v)
    exact N.model_metric.symm (e x) _ _
  have hpos : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) R,
      ∀ v, v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    apply N.model_metric.pos (e x)
    intro hz
    apply hv
    apply (hi x hx).injective
    rw [map_zero]
    convert! hz using 1
  let s : ℝ := (ρ + R) / 2
  have hρs : ρ < s := by
    dsimp [s]
    linarith
  have hsR : s < R := by
    dsimp [s]
    linarith
  obtain ⟨gE, DE, heq, hG⟩ :=
    CoordinateExponential.exists_gauss_metric_extension hρ hρs hsR B hB hsymm hpos hgauss
  have hzeroE : christoffelBilinear gE.euclideanCoefficients 0 = 0 := by
    have h := gauss_center_coordinate_connection_zero DE hG
    simpa [DE.coordinateConnectionCoefficient_model] using h
  have hEq : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ,
      gE.euclideanCoefficients y = B y := by
    intro y hy
    exact heq y hy
  have hEq0 : gE.euclideanCoefficients 0 = B 0 := hEq 0 (by simp [hρ.le])
  have hEqNhds : B =ᶠ[𝓝 (0 : EuclideanSpace ℝ (Fin 3))]
      gE.euclideanCoefficients := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy
    exact (hEq y (mem_closedBall.mpr (le_of_lt (mem_ball.mp hy)))).symm
  have hDeriv : fderiv ℝ B 0 = fderiv ℝ gE.euclideanCoefficients 0 :=
    hEqNhds.fderiv_eq
  have hChrist : christoffelBilinear B 0 =
      christoffelBilinear gE.euclideanCoefficients 0 := by
    unfold christoffelBilinear
    rw [hEq0.symm, hDeriv]
  rw [hChrist, hzeroE]

end PoincareConjecture.M28.tube
