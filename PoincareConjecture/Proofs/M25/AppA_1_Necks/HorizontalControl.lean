import PoincareConjecture.Proofs.M25.AppA_1_Necks.AxialVector
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Pairing
import Mathlib.Analysis.Normed.Module.RCLike.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}




theorem normalizedAxialVector_pairing_error (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    |g.inner x v (N.normalizedAxialVector x) -
      N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
      2 * N.epsilon * g.tangentNorm x v := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let L : TangentSpace (𝓡 3) x →ₗ[ℝ] ℝ :=
    (g.inner x).toBilinForm.flip (N.normalizedAxialVector x) -
      N.scale • (mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x).toLinearMap
  have hunit (w : TangentSpace (𝓡 3) x) (hw : w ∈ Metric.sphere 0 1) :
      ‖L w‖ ≤ 2 * N.epsilon := by
    have hn : g.tangentNorm x w = 1 := mem_sphere_zero_iff_norm.mp hw
    exact N.axial_pairing_error hx w hn
  have h := LinearMap.bound_of_sphere_bound (𝕜 := ℝ) (E := TangentSpace (𝓡 3) x)
    (r := 1) (by norm_num) (2 * N.epsilon) L hunit v
  change |g.inner x v (N.normalizedAxialVector x) -
    N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
    (2 * N.epsilon) / 1 * g.tangentNorm x v at h
  simpa only [div_one] using h




theorem exists_intersecting_axial_covector_control {η : ℝ} (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ N.carrier → x ∈ N'.carrier →
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ v : TangentSpace (𝓡 3) x,
        |N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x v -
          σ * (N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v)| ≤
          η * g.tangentNorm x v := by
  obtain ⟨εa, hapos, hacap, haxis⟩ := exists_intersecting_axial_control.{u} (half_pos hη)
  refine ⟨min εa (η / 8), lt_min hapos (by positivity),
    (min_le_left _ _).trans hacap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' x hx hx'
  obtain ⟨σ, hσ, hclose⟩ := haxis N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _)) x hx hx'
  refine ⟨σ, hσ, ?_⟩
  intro v
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let a := N.normalizedAxialVector x
  let a' := N'.normalizedAxialVector x
  let l := N.scale * mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v
  let l' := N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x v
  have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hpair := N.normalizedAxialVector_pairing_error hx v
  have hpair' := N'.normalizedAxialVector_pairing_error hx' v
  have hcs : |g.inner x v (a' - σ • a)| ≤ g.tangentNorm x v * (η / 2) := by
    exact (abs_real_inner_le_norm v (a' - σ • a)).trans
      (mul_le_mul_of_nonneg_left hclose.le (Real.sqrt_nonneg _))
  have heq : l' - σ * l = -(g.inner x v a' - l') +
      g.inner x v (a' - σ • a) + σ * (g.inner x v a - l) := by
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  have hbudget : 2 * N'.epsilon + η / 2 + 2 * N.epsilon ≤ η := by
    have hn := hN.trans (min_le_right _ _)
    have hn' := hN'.trans (min_le_right _ _)
    linarith
  change |l' - σ * l| ≤ η * g.tangentNorm x v
  calc
    _ ≤ |g.inner x v a' - l'| + |g.inner x v (a' - σ • a)| +
        |g.inner x v a - l| := by
      rw [heq]
      simpa only [abs_neg, abs_mul, habsσ, one_mul] using
        (abs_add_le (-(g.inner x v a' - l') + g.inner x v (a' - σ • a))
          (σ * (g.inner x v a - l))).trans
            (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * N'.epsilon * g.tangentNorm x v + g.tangentNorm x v * (η / 2) +
        2 * N.epsilon * g.tangentNorm x v := add_le_add (add_le_add hpair' hcs) hpair
    _ = (2 * N'.epsilon + η / 2 + 2 * N.epsilon) * g.tangentNorm x v := by ring
    _ ≤ η * g.tangentNorm x v :=
      mul_le_mul_of_nonneg_right hbudget (Real.sqrt_nonneg _)




theorem exists_intersecting_horizontal_control {η : ℝ} (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ x : M, x ∈ N.carrier → x ∈ N'.carrier →
      ∀ v : TangentSpace (𝓡 3) x,
      mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v = 0 →
        |N'.scale * mvfderiv (𝓡 3) (fun y => (N'.coordinate_inverse y).2) x v| ≤
          η * g.tangentNorm x v := by
  obtain ⟨ε, hpos, hcap, hcontrol⟩ := exists_intersecting_axial_covector_control.{u} hη
  refine ⟨ε, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' x hx hx' v hv
  obtain ⟨σ, _, h⟩ := hcontrol N N' hN hN' x hx hx'
  simpa only [hv, mul_zero, sub_zero] using h v

end PoincareConjecture.EpsilonNeck
