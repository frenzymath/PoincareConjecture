import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialTransition


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.EpsilonNeck

private theorem fixed_axial_bounds
    {s t X Z G R a b : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : a ≤ 1 / 200) (hb : b ≤ 1 / 200)
    (hst : s ≤ 2 * t) (hts : t ≤ 2 * s) (hZ : Z ^ 2 ≤ X)
    (hlo : (1 - a) * s * X ≤ G) (hhi : G ≤ (1 + a) * s * X)
    (hlo' : (1 - b) * t ≤ G) (hhi' : G ≤ (1 + b) * t)
    (hRlo : (9 / 25 : ℝ) * X - (1 / 2 : ℝ) * Z ^ 2 ≤ R)
    (hRhi : R ≤ 7 / 50) : (1 / 4 : ℝ) ≤ |Z| ∧ |Z| ≤ (3 / 2 : ℝ) := by
  have hX : 0 ≤ X := (sq_nonneg Z).trans hZ
  have hlow : (199 / 200 : ℝ) * s * X ≤ G := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hs.le hX)]
  have hhigh : G ≤ (201 / 200 : ℝ) * s * X := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hs.le hX)]
  have hlow' : (199 / 200 : ℝ) * t ≤ G := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) ht.le]
  have hhigh' : G ≤ (201 / 200 : ℝ) * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) ht.le]
  have hXlow : (49 / 100 : ℝ) ≤ X := by
    by_contra h
    have hp := mul_pos hs (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hXhigh : X ≤ (41 / 20 : ℝ) := by
    by_contra h
    have hp := mul_pos hs (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  constructor
  · by_contra h
    have habs : |Z| < (1 / 4 : ℝ) := lt_of_not_ge h
    nlinarith [sq_abs Z, abs_nonneg Z]
  · by_contra h
    have habs : (3 / 2 : ℝ) < |Z| := lt_of_not_ge h
    nlinarith [sq_abs Z, abs_nonneg Z]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem axial_transition_bounds_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier ∩ P.carrier) :
    let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      P.coordinate_map (P.coordinate_inverse x) (0, 1)
    let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
    (1 / 4 : ℝ) ≤ |u.2| ∧ |u.2| ≤ (3 / 2 : ℝ) := by
  let D := N.connection
  let z := N.coordinate_inverse x
  let z' := P.coordinate_inverse x
  let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) P.coordinate_map z' (0, 1)
  let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
  let X := EvolvingRoundCylinderMetric 0 z u u
  have hz : z ∈ N.cylinderDomain := N.coordinate_inverse_mem x hx.1
  have hz' : z' ∈ P.cylinderDomain := P.coordinate_inverse_mem x hx.2
  have hmap : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u = w :=
    N.coordinate_map_mfderiv_inverse_prod hx.1 w
  have hmapx : N.coordinate_map z = x := N.coordinate_map_coordinate_inverse hx.1
  have hmapx' : P.coordinate_map z' = x := P.coordinate_map_coordinate_inverse hx.2
  have hunit : EvolvingRoundCylinderMetric 0 z' (0, 1) (0, 1) = 1 := by
    simp [EvolvingRoundCylinderMetric]
  have hZ : u.2 ^ 2 ≤ X := by
    have hhor : 0 ≤ inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 u.1)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 u.1) :=
      real_inner_self_nonneg
    dsimp [X, EvolvingRoundCylinderMetric]
    nlinarith
  have hmetric := N.pullback_metric_bounds hz.2 u
  change (1 - N.epsilon) * N.scale ^ 2 * X ≤
      g.inner (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u) ∧
      g.inner (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u) ≤
      (1 + N.epsilon) * N.scale ^ 2 * X at hmetric
  rw [hmap, hmapx] at hmetric
  have hmetric' := P.pullback_metric_bounds hz'.2 (0, 1)
  rw [hunit, mul_one, mul_one] at hmetric'
  change (1 - P.epsilon) * P.scale ^ 2 ≤ g.inner (P.coordinate_map z') w w ∧
    g.inner (P.coordinate_map z') w w ≤ (1 + P.epsilon) * P.scale ^ 2 at hmetric'
  rw [hmapx'] at hmetric'
  have hricciN := N.ricci_quadratic_control_of_epsilon_le D hN z hz u
  rw [hmap, hmapx] at hricciN
  have hricciP := P.ricci_quadratic_control_of_epsilon_le D hP z' hz' (0, 1)
  rw [hunit, hmapx'] at hricciP
  have hRlo : (9 / 25 : ℝ) * X - (1 / 2 : ℝ) * u.2 ^ 2 ≤ D.ricci x w w := by
    have h := (abs_le.mp hricciN).1
    change -(7 / 50 * X) ≤ D.ricci x w w - 1 / 2 * (X - u.2 ^ 2) at h
    linarith
  have hRhi : D.ricci x w w ≤ 7 / 50 := by
    have h := (abs_le.mp hricciP).2
    change D.ricci x w w - 1 / 2 * (1 - (1 : ℝ) ^ 2) ≤ 7 / 50 * 1 at h
    norm_num at h
    exact h
  exact fixed_axial_bounds (sq_pos_of_pos N.scale_pos) (sq_pos_of_pos P.scale_pos)
    hN hP (P.scale_sq_le_twice_of_common_point N hP hN hx.2 hx.1)
    (N.scale_sq_le_twice_of_common_point P hN hP hx.1 hx.2) hZ
    hmetric.1 hmetric.2 hmetric'.1 hmetric'.2 hRlo hRhi

theorem transition_axis_deriv_bounds_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹)
    (hx : P.coordinate_map (q, s) ∈ N.carrier) :
    (1 / 4 : ℝ) ≤ |deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2) s| ∧
      |deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2) s| ≤ (3 / 2 : ℝ) := by
  have hz : (q, s) ∈ P.cylinderDomain := ⟨mem_univ _, hs⟩
  have h := N.axial_transition_bounds_of_epsilon_le P hN hP ⟨hx, P.coordinate_map_mem hz⟩
  rw [P.coordinate_inverse_coordinate_map hz] at h
  rw [(N.transition_axis_hasDerivAt P q hs hx).deriv]
  exact h

end PoincareConjecture.EpsilonNeck
