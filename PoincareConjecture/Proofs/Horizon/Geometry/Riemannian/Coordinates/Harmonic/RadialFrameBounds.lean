import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrameComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.FrameEnergy









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}




theorem exists_small_radial_frame_of_gauss {R K ε : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K) (hε : 0 < ε) :
    let c : ℝ := (9 / 4) * K
    let S : ℝ := 1 + 9 * ((n : ℝ) + 1) * K
    ∃ r : ℝ, 0 < r ∧ 2 * r ≤ R ∧ r ≤ 1 ∧
      let δ := c * r ^ 2
      let s := S * r ^ 2
      0 ≤ δ ∧ δ ≤ 1 ∧ δ ≤ ε ∧ δ * (2 + δ) ≤ ε ∧ 2 * δ ≤ ε ∧
        0 < s ∧ s ≤ ε ∧ r ^ 2 * (n : ℝ) * K ≤ s ∧
        (81 / 4 : ℝ) * n * K ^ 2 * r ^ 2 ≤ (s / r) ^ 2 ∧
        ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
          (∀ x w, g.euclideanCoefficients x x w = inner ℝ x w) →
          (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
              g.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) →
          (∀ x ∈ Metric.ball 0 R, D.curvatureTensorNorm x ≤ K) →
          ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
              EuclideanSpace ℝ (Fin n),
            ContDiff ℝ ∞ T ∧ T 0 = ContinuousLinearMap.id ℝ _ ∧
            (∀ x, (T x).IsInvertible) ∧
            (∀ x v w, g.inner x (T x v) (T x w) = inner ℝ v w) ∧
            (∀ x ∈ Metric.closedBall 0 r, ∀ v,
              ‖(T x).inverse v - v‖ ≤ δ * ‖v‖) ∧
            (∀ x ∈ Metric.closedBall 0 r, ∀ v : EuclideanSpace ℝ (Fin n),
              |g.inner x v v - ‖v‖ ^ 2| ≤ δ * (2 + δ) * ‖v‖ ^ 2) ∧
            (∀ x ∈ Metric.closedBall 0 r, ∀ i : Fin n,
              g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from
                D.gradient (fun y => y i) x) - T x (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤
                2 * δ) ∧
            (∀ x, ∀ i : Fin n,
              g.tangentNorm x (T x (EuclideanSpace.basisFun (Fin n) ℝ i)) = 1) ∧
            (∀ x ∈ Metric.closedBall 0 r, ∀ i : Fin n,
              (∑ j, g.inner x
                (D.connection (fun y => T y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
                  (g.orthonormalBasis x j))
                (D.connection (fun y => T y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
                  (g.orthonormalBasis x j))) ≤ (81 / 4 : ℝ) * n * K ^ 2 * r ^ 2) := by
  let c : ℝ := (9 / 4) * K
  let S : ℝ := 1 + 9 * ((n : ℝ) + 1) * K
  let τ : ℝ := min 1 (ε / 3)
  let r : ℝ := min (R / 2) (min 1 (τ / (1 + S + c)))
  let δ : ℝ := c * r ^ 2
  let s : ℝ := S * r ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hτ : 0 < τ := lt_min (by norm_num) (by positivity)
  have hden : 0 < 1 + S + c := by positivity
  have hr : 0 < r := lt_min (by positivity) (lt_min (by norm_num) (div_pos hτ hden))
  have hrR : r ≤ R / 2 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hratio : r ≤ τ / (1 + S + c) := (min_le_right _ _).trans (min_le_right _ _)
  have hrsmall : (1 + S + c) * r ≤ τ := by
    have h := (le_div_iff₀ hden).mp hratio
    nlinarith
  have hrsq : r ^ 2 ≤ r := by nlinarith
  have hδ0 : 0 ≤ δ := mul_nonneg hc (sq_nonneg r)
  have hδτ : δ ≤ τ := by
    calc
      _ ≤ c * r := mul_le_mul_of_nonneg_left hrsq hc
      _ ≤ (1 + S + c) * r := mul_le_mul_of_nonneg_right (by linarith) hr.le
      _ ≤ τ := hrsmall
  have hsτ : s ≤ τ := by
    calc
      _ ≤ S * r := mul_le_mul_of_nonneg_left hrsq hS.le
      _ ≤ (1 + S + c) * r := mul_le_mul_of_nonneg_right (by linarith) hr.le
      _ ≤ τ := hrsmall
  have hδ1 : δ ≤ 1 := hδτ.trans (min_le_left _ _)
  have hδ3 : 3 * δ ≤ ε := by
    have h := hδτ.trans (min_le_right _ _)
    linarith
  have hδmetric : δ * (2 + δ) ≤ ε := by nlinarith
  have hs : 0 < s := mul_pos hS (sq_pos_of_pos hr)
  have hsε : s ≤ ε := by
    have h := hsτ.trans (min_le_right _ _)
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hSK : (n : ℝ) * K ≤ S := by
    dsimp [S]
    nlinarith [mul_nonneg hn hK]
  have hSsq : (81 / 4 : ℝ) * n * K ^ 2 ≤ S ^ 2 := by
    have hp : 0 ≤ 9 * ((n : ℝ) + 1) * K := by positivity
    have hle : 9 * ((n : ℝ) + 1) * K ≤ S := by dsimp [S]; linarith
    have hsq := (sq_le_sq₀ hp hS.le).mpr hle
    nlinarith [sq_nonneg ((n : ℝ) * K), mul_nonneg hn (sq_nonneg K), sq_nonneg K]
  have hscale : r ^ 2 * (n : ℝ) * K ≤ s := by
    have h := mul_le_mul_of_nonneg_right hSK (sq_nonneg r)
    dsimp only [s]
    nlinarith
  have hconnscale : (81 / 4 : ℝ) * n * K ^ 2 * r ^ 2 ≤ (s / r) ^ 2 := by
    have heq : s / r = S * r := by dsimp [s]; field_simp
    rw [heq, mul_pow]
    exact mul_le_mul_of_nonneg_right hSsq (sq_nonneg r)
  refine ⟨r, hr, by linarith, hr1, hδ0, hδ1, by change δ ≤ ε; linarith, hδmetric,
    by change 2 * δ ≤ ε; linarith, hs, hsε, hscale, hconnscale,
    fun g D hgauss hell hcurv => ?_⟩
  have hmetric : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.tangentNorm x v ≤ (3 / 2 : ℝ) * ‖v‖ := by
    intro x hx v
    have h := Real.sqrt_le_sqrt (hell x hx v).2
    have heq : (9 / 4 : ℝ) * ‖v‖ ^ 2 = ((3 / 2 : ℝ) * ‖v‖) ^ 2 := by ring
    rw [heq, Real.sqrt_sq (by positivity)] at h
    exact h
  obtain ⟨T, hT, hT0, hTi, hiso, hconnection, hcoframe⟩ :=
    exists_radial_frame_of_gauss D hgauss hK (by norm_num : (0 : ℝ) ≤ 3 / 2) hcurv hmetric
  have hnorm {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall 0 r) : ‖x‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hball {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.closedBall 0 r) :
      x ∈ Metric.ball 0 R := by
    simp only [Metric.mem_ball, dist_zero_right]
    have h := hnorm hx
    linarith
  have hclose (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.closedBall 0 r)
      (v : EuclideanSpace ℝ (Fin n)) : ‖(T x).inverse v - v‖ ≤ δ * ‖v‖ := by
    calc
      _ ≤ K * (3 / 2 : ℝ) ^ 2 * ‖x‖ ^ 2 * ‖v‖ := hcoframe x (hball hx) v
      _ ≤ K * (3 / 2 : ℝ) ^ 2 * r ^ 2 * ‖v‖ := by gcongr; exact hnorm hx
      _ = _ := by dsimp [δ, c]; ring
  refine ⟨T, hT, hT0, hTi, hiso, hclose, ?_, ?_, ?_, ?_⟩
  · intro x hx v
    exact inner_self_sub_norm_sq_le_of_frame_inverse x (hTi x) (hiso x) hδ0 (hclose x hx) v
  · intro x hx i
    have h := gradient_coordinate_sub_frame_norm_le D x (hTi x) (hiso x)
      (by norm_num : (0 : ℝ) < 1 / 4) hδ0
      (fun v => (hell x (hball hx) v).1) (hclose x hx) i
    have hratio : δ / Real.sqrt (1 / 4 : ℝ) = 2 * δ := by
      norm_num [Real.sqrt_div]
      ring
    rw [hratio] at h
    exact h
  · intro x i
    change Real.sqrt (g.inner x (T x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (T x (EuclideanSpace.basisFun (Fin n) ℝ i))) = 1
    rw [hiso, real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one]
    norm_num
  · intro x hx i
    have hdir (w : EuclideanSpace ℝ (Fin n)) :
        g.tangentNorm x (D.connection (fun y => T y (EuclideanSpace.basisFun (Fin n) ℝ i)) x w) ≤
          (c * r) * ‖w‖ := by
      have h := hconnection x (hball hx) (EuclideanSpace.basisFun (Fin n) ℝ i) w
      rw [OrthonormalBasis.norm_eq_one, mul_one] at h
      calc
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * ‖x‖ * ‖w‖ := h
        _ ≤ K * (3 / 2 : ℝ) ^ 2 * r * ‖w‖ := by gcongr; exact hnorm hx
        _ = _ := by dsimp [c]; ring
    have h := D.connection_energy_le_of_directional_bound
      (fun y => T y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
      (by norm_num : (0 : ℝ) < 1 / 4) (fun v => (hell x (hball hx) v).1) hdir
    calc
      _ ≤ (n : ℝ) * (c * r) ^ 2 / (1 / 4) := h
      _ = _ := by dsimp [c]; ring

end PoincareConjecture.HarmonicCoordinates
