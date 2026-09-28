import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierScale
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.Quadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

private theorem axial_bounds_of_scalar_metric_ricci
    {s t X Z G R Q a b : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : a ≤ 1 / 200) (hb : b ≤ 1 / 200)
    (hscalar : |s * Q - 1| ≤ 1 / 100) (hscalar' : |t * Q - 1| ≤ 1 / 100)
    (hZ : Z ^ 2 ≤ X)
    (hlo : (1 - a) * s * X ≤ G) (hhi : G ≤ (1 + a) * s * X)
    (hlo' : (1 - b) * t ≤ G) (hhi' : G ≤ (1 + b) * t)
    (hRlo : (49 / 100 : ℝ) * X - (1 / 2 : ℝ) * Z ^ 2 ≤ R)
    (hRhi : R ≤ 1 / 100) :
    (0.9 : ℝ) ≤ |Z| ∧ |Z| ≤ (1.1 : ℝ) := by
  have hX : 0 ≤ X := (sq_nonneg Z).trans hZ
  have hsq := abs_le.mp hscalar
  have htq := abs_le.mp hscalar'
  have hQ : 0 < Q := by
    by_contra h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_gt h)
    linarith
  have hst : (0.95 : ℝ) * s ≤ t := by
    apply (mul_le_mul_iff_left₀ hQ).mp
    nlinarith
  have hts : t ≤ (1.05 : ℝ) * s := by
    apply (mul_le_mul_iff_left₀ hQ).mp
    nlinarith
  have hlow : (0.995 : ℝ) * s * X ≤ G := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hs.le hX)]
  have hhigh : G ≤ (1.005 : ℝ) * s * X := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hs.le hX)]
  have hlow' : (0.995 : ℝ) * t ≤ G := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) ht.le]
  have hhigh' : G ≤ (1.005 : ℝ) * t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) ht.le]
  have hXlow : (0.9 : ℝ) ≤ X := by
    by_contra h
    have hp := mul_pos hs (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  have hXhigh : X ≤ (1.1 : ℝ) := by
    by_contra h
    have hp := mul_pos hs (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  constructor
  · by_contra h
    have habs : |Z| < (0.9 : ℝ) := lt_of_not_ge h
    have hzsq : Z ^ 2 < (0.9 : ℝ) ^ 2 := by nlinarith [sq_abs Z, abs_nonneg Z]
    nlinarith
  · by_contra h
    have habs : (1.1 : ℝ) < |Z| := lt_of_not_ge h
    nlinarith [sq_abs Z, abs_nonneg Z]

theorem exists_axial_transition_bounds_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ x ∈ N.carrier ∩ N'.carrier,
          let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            N'.coordinate_map (N'.coordinate_inverse x) (0, 1)
          let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
          (0.9 : ℝ) ≤ |u.2| ∧ |u.2| ≤ (1.1 : ℝ) := by
  obtain ⟨ε₁, hε₁, hsmall, hscalar⟩ :=
    exists_ambient_scalar_control_on_closure_m28.{u} (show (0 : ℝ) < 1 / 100 by norm_num)
  obtain ⟨ε₂, hε₂, _, hricci⟩ := exists_ricci_quadratic_control.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' x hx
  let D := N.connection
  let z := N.coordinate_inverse x
  let z' := N'.coordinate_inverse x
  let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z' (0, 1)
  let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
  let X := EvolvingRoundCylinderMetric 0 z u u
  have hz : z ∈ N.cylinderDomain := N.coordinate_inverse_mem x hx.1
  have hz' : z' ∈ N'.cylinderDomain := N'.coordinate_inverse_mem x hx.2
  have hmap : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u = w :=
    N.coordinate_map_mfderiv_inverse_prod hx.1 w
  have hmapx : N.coordinate_map z = x := N.coordinate_map_coordinate_inverse hx.1
  have hmapx' : N'.coordinate_map z' = x := N'.coordinate_map_coordinate_inverse hx.2
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
  have hmetric' := N'.pullback_metric_bounds hz'.2 (0, 1)
  rw [hunit, mul_one, mul_one] at hmetric'
  change (1 - N'.epsilon) * N'.scale ^ 2 ≤ g.inner (N'.coordinate_map z') w w ∧
    g.inner (N'.coordinate_map z') w w ≤ (1 + N'.epsilon) * N'.scale ^ 2 at hmetric'
  rw [hmapx'] at hmetric'
  have hricciN := hricci N D (hN.trans (min_le_right _ _)) z hz u
  rw [hmap, hmapx] at hricciN
  have hricciN' := hricci N' D (hN'.trans (min_le_right _ _)) z' hz' (0, 1)
  rw [hunit, hmapx'] at hricciN'
  have hRlo : (49 / 100 : ℝ) * X - (1 / 2 : ℝ) * u.2 ^ 2 ≤ D.ricci x w w := by
    have h := (abs_le.mp hricciN).1
    change -(1 / 100 * X) ≤ D.ricci x w w - 1 / 2 * (X - u.2 ^ 2) at h
    linarith
  have hRhi : D.ricci x w w ≤ 1 / 100 := by
    have h := (abs_le.mp hricciN').2
    change D.ricci x w w - 1 / 2 * (1 - (1 : ℝ) ^ 2) ≤ 1 / 100 * 1 at h
    norm_num at h
    exact h
  exact axial_bounds_of_scalar_metric_ricci (sq_pos_of_pos N.scale_pos)
    (sq_pos_of_pos N'.scale_pos)
    ((hN.trans (min_le_left _ _)).trans hsmall)
    ((hN'.trans (min_le_left _ _)).trans hsmall)
    (hscalar N D (hN.trans (min_le_left _ _)) x (subset_closure hx.1))
    (hscalar N' D (hN'.trans (min_le_left _ _)) x (subset_closure hx.2))
    hZ hmetric.1 hmetric.2 hmetric'.1 hmetric'.2 hRlo hRhi

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem transition_axis_hasDerivAt_m28 (N N' : EpsilonNeck g) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N'.coordinate_map (q, s) ∈ N.carrier) :
    HasDerivAt (fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse
        (N'.coordinate_map (q, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, s) (0, 1))).2 s := by
  have hmap := (N'.coordinate_map_smooth.contMDiffAt
    (N'.cylinderDomain_open.mem_nhds
      (show (q, s) ∈ N'.cylinderDomain from ⟨mem_univ _, hs⟩))).mdifferentiableAt (by simp)
  have hinv := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hpair := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) q s).prodMk
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) s)
  have hcomp := hinv.hasMFDerivAt.comp s (hmap.hasMFDerivAt.comp s hpair)
  have hsnd := (hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
    (N.coordinate_inverse (N'.coordinate_map (q, s)))).comp s hcomp
  exact hsnd.hasFDerivAt.hasDerivAt

theorem exists_transition_axis_deriv_bounds_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        N'.coordinate_map (q, s) ∈ N.carrier →
          (0.9 : ℝ) ≤ |deriv
            (fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2) s| ∧
          |deriv (fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2) s| ≤
            (1.1 : ℝ) := by
  obtain ⟨ε₀, hε₀, hsmall, hbounds⟩ := exists_axial_transition_bounds_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' q s hs hx
  have hz : (q, s) ∈ N'.cylinderDomain := ⟨mem_univ _, hs⟩
  have h := hbounds N N' hN hN' (N'.coordinate_map (q, s))
    ⟨hx, N'.coordinate_map_mem hz⟩
  rw [N'.coordinate_inverse_coordinate_map hz] at h
  rw [(N.transition_axis_hasDerivAt_m28 N' q hs hx).deriv]
  exact h

end PoincareConjecture.EpsilonNeck
