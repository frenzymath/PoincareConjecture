import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

private theorem endpoint_curvature_coefficient_le_neg {κ ρ C : ℝ}
    (hκ : 0 < κ) (hρ : 0 < ρ) (hC : 0 < C) (hρC : ρ ≤ C)
    (hlarge : 6 / (κ * ρ) ≤ C) :
    1 / C - κ * C * ((1 - (1 - ρ / C) ^ 3) / 3) ≤ -(κ * ρ / 6) := by
  have hx0 : 0 ≤ ρ / C := div_nonneg hρ.le hC.le
  have hx1 : ρ / C ≤ 1 := (div_le_one hC).mpr hρC
  have hy0 : 0 ≤ 1 - ρ / C := sub_nonneg.mpr hx1
  have hy1 : 1 - ρ / C ≤ 1 := sub_le_self _ hx0
  have hy2 : (1 - ρ / C) ^ 2 ≤ 1 := by nlinarith
  have hy3 : (1 - ρ / C) ^ 3 ≤ 1 - ρ / C := by
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  have hpoly : ρ / C / 3 ≤ (1 - (1 - ρ / C) ^ 3) / 3 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hκ.le hC.le)
  have hcancel : κ * C * (ρ / C / 3) = κ * ρ / 3 := by field_simp
  rw [hcancel] at hmul
  have hlarge' : 6 ≤ C * (κ * ρ) := (div_le_iff₀ (mul_pos hκ hρ)).mp hlarge
  have herror : 1 / C ≤ κ * ρ / 6 := by
    apply (div_le_div_iff₀ hC (by norm_num : (0 : ℝ) < 6)).mpr
    nlinarith only [hlarge']
  linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_transverse_distance_upper_support_of_endpoint_ball_curvature
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (x : M) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hball : ∀ y, (g.edist y x).toReal ≤ ρ → ∀ u v,
      κ * (g.inner y u u * g.inner y v v - (g.inner y u v) ^ 2) ≤
        D.curvatureTensor y u v u v)
    (p : M) (hp : max (4 * ρ / 3) (8 / (κ * ρ)) ≤ (g.edist p x).toReal) :
    ∃ (U : Set M) (f : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
      f x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ f y) ∧
      g.inner x (D.gradient f x) (D.gradient f x) = 1 ∧
      ∀ w : TangentSpace (𝓡 n) x,
        D.hessian f x w w ≤
          -(min (κ * ρ / 6) 1) * (g.inner x w w - (mvfderiv (𝓡 n) f x w) ^ 2) := by
  let a := min (κ * ρ / 6) 1
  let L := max (4 * ρ / 3) (8 / (κ * ρ))
  have hL : 0 < L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hd : 0 < (g.edist p x).toReal := hL.trans_le hp
  have hpx : p ≠ x := by
    rintro rfl
    let := g.toMetricSpace
    change 0 < (EDist.edist p p).toReal at hd
    simp at hd
  have hρd : ρ ≤ (3 / 4) * (g.edist p x).toReal := by
    have h := (le_max_left _ _).trans hp
    change 4 * ρ / 3 ≤ (g.edist p x).toReal at h
    linarith
  have hlarge : 6 / (κ * ρ) ≤ (3 / 4) * (g.edist p x).toReal := by
    have h := (le_max_right _ _).trans hp
    change 8 / (κ * ρ) ≤ (g.edist p x).toReal at h
    have heq : 6 / (κ * ρ) = (3 / 4) * (8 / (κ * ρ)) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  obtain ⟨U, f, hU, hx, hf, htouch, hmajor, hunit, hhess⟩ :=
    g.exists_distance_hessian_upper_support_of_endpoint_ball_curvature
      D hcomplete hsec p x hpx hρ.le hρd hball
  refine ⟨U, f, hU, hx, hf, htouch, hmajor, hunit, ?_⟩
  intro w
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have htrans : 0 ≤ g.inner x w w - (mvfderiv (𝓡 n) f x w) ^ 2 := by
    have hcs := real_inner_mul_inner_self_le (D.gradient f x) w
    change g.inner x (D.gradient f x) w * g.inner x (D.gradient f x) w ≤
      g.inner x (D.gradient f x) (D.gradient f x) * g.inner x w w at hcs
    rw [hunit, one_mul, D.inner_gradient] at hcs
    nlinarith only [hcs]
  have hc := endpoint_curvature_coefficient_le_neg hκ hρ
    (mul_pos (by norm_num) hd) hρd hlarge
  have hca : -(κ * ρ / 6) ≤ -a := neg_le_neg (min_le_left _ _)
  exact (hhess w).trans (mul_le_mul_of_nonneg_right (hc.trans hca) htrans)

theorem exists_uniform_transverse_distance_upper_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (x : M)
    (hpos : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ L : ℝ, 0 < L ∧
      ∀ p : M, L ≤ (g.edist p x).toReal →
        ∃ (U : Set M) (f : M → ℝ), IsOpen U ∧ x ∈ U ∧
          ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
          f x = (g.edist p x).toReal ∧
          (∀ y ∈ U, (g.edist p y).toReal ≤ f y) ∧
          g.inner x (D.gradient f x) (D.gradient f x) = 1 ∧
          ∀ w : TangentSpace (𝓡 n) x,
            D.hessian f x w w ≤
              -a * (g.inner x w w - (mvfderiv (𝓡 n) f x w) ^ 2) := by
  obtain ⟨κ, hκ, ρ, hρ, hball⟩ :=
    D.exists_pos_curvatureTensor_lower_bound_on_edist_ball x hpos
  refine ⟨min (κ * ρ / 6) 1, lt_min (by positivity) zero_lt_one,
    min_le_right _ _, max (4 * ρ / 3) (8 / (κ * ρ)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  exact fun p hp => g.exists_transverse_distance_upper_support_of_endpoint_ball_curvature
    D hcomplete hsec x hκ hρ hball p hp

theorem exists_uniform_transverse_distance_upper_support_on_edist_ball
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (x : M)
    (hpos : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ L : ℝ, 0 < L ∧ ∃ r : ℝ, 0 < r ∧
      ∀ y : M, (g.edist y x).toReal ≤ r →
        ∀ p : M, L ≤ (g.edist p x).toReal →
          ∃ (U : Set M) (f : M → ℝ), IsOpen U ∧ y ∈ U ∧
            ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U ∧
            f y = (g.edist p y).toReal ∧
            (∀ z ∈ U, (g.edist p z).toReal ≤ f z) ∧
            g.inner y (D.gradient f y) (D.gradient f y) = 1 ∧
            ∀ w : TangentSpace (𝓡 n) y,
              D.hessian f y w w ≤
                -a * (g.inner y w w - (mvfderiv (𝓡 n) f y w) ^ 2) := by
  obtain ⟨κ, hκ, R, hR, hball⟩ :=
    D.exists_pos_curvatureTensor_lower_bound_on_edist_ball x hpos
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  let L := max (4 * ρ / 3) (8 / (κ * ρ))
  have hL : 0 < L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨min (κ * ρ / 6) 1, lt_min (by positivity) zero_lt_one,
    min_le_right _ _, L + ρ, add_pos hL hρ, ρ, hρ, ?_⟩
  intro y hy p hp
  have hball_y : ∀ z, (g.edist z y).toReal ≤ ρ → ∀ u v,
      κ * (g.inner z u u * g.inner z v v - (g.inner z u v) ^ 2) ≤
        D.curvatureTensor z u v u v := by
    intro z hz u v
    apply hball z ?_ u v
    have ht := g.toReal_edist_triangle z y x
    change (g.edist y x).toReal ≤ R / 2 at hy
    change (g.edist z y).toReal ≤ R / 2 at hz
    linarith
  have hpy : L ≤ (g.edist p y).toReal := by
    have ht := g.toReal_edist_triangle p y x
    linarith
  exact g.exists_transverse_distance_upper_support_of_endpoint_ball_curvature
    D hcomplete hsec y hκ hρ hball_y p hpy

end PoincareConjecture.RiemannianMetric
