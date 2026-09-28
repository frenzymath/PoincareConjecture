import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.Quadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.SliceProjection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

private theorem zero_of_fixed_metric_ricci_bounds {s t X Y G R : ℝ}
    (hs : 0 < s) (hscale : t ^ 2 ≤ 2 * s ^ 2) (hY : 0 ≤ Y)
    (hlo : (199 / 200 : ℝ) * s ^ 2 * X ≤ G)
    (hhi : G ≤ (201 / 200 : ℝ) * t ^ 2 * Y)
    (hRlo : (9 / 25 : ℝ) * Y ≤ R) (hRhi : R ≤ (7 / 50 : ℝ) * X) : Y = 0 := by
  have hcomp : s ^ 2 * ((199 / 200 : ℝ) * X) ≤
      s ^ 2 * ((201 / 100 : ℝ) * Y) := by
    nlinarith [mul_le_mul_of_nonneg_right hscale hY]
  have hXY := (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp hcomp
  linarith

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem scale_sq_le_twice_of_common_point
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 200)
    (hε' : N'.epsilon ≤ 1 / 200) {x : M} (hx : x ∈ N.carrier)
    (hx' : x ∈ N'.carrier) : N'.scale ^ 2 ≤ 2 * N.scale ^ 2 := by
  have hl := (abs_lt.mp
    (N.abs_scaled_scalar_sub_one_lt_third_on_carrier N.connection hε hx)).1
  have hu := (abs_lt.mp
    (N'.abs_scaled_scalar_sub_one_lt_third_on_carrier N.connection hε' hx')).2
  have hl' : (2 / 3 : ℝ) ≤ N.scale ^ 2 * N.connection.scalarCurvature x := by linarith
  have hu' : N'.scale ^ 2 * N.connection.scalarCurvature x ≤ (4 / 3 : ℝ) := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hl' (sq_nonneg N'.scale)
  have h₂ := mul_le_mul_of_nonneg_left hu' (sq_nonneg N.scale)
  nlinarith

theorem sphereSlice_projection_mfderiv_bijective_of_epsilon_le
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 200)
    (hε' : N'.epsilon ≤ 1 / 200) {a : ℝ}
    (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹) (q : UnitTwoSphere)
    (hx : N'.coordinate_map (q, a) ∈ N.carrier) :
    Function.Bijective (mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q) := by
  let D := N.connection
  let A := mfderiv (𝓡 2) (𝓡 2)
    (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q
  have hscale := N.scale_sq_le_twice_of_common_point N' hε hε' hx
    (N'.coordinate_map_mem ⟨mem_univ _, ha⟩)
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    let x := N'.coordinate_map (q, a)
    let z := N.coordinate_inverse x
    let w : TangentSpace (𝓡 3) x :=
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, a) (v, 0)
    let u : RoundCylinderTangent z :=
      mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
    let X := EvolvingRoundCylinderMetric 0 z u u
    let Y := EvolvingRoundCylinderMetric 0 (q, a) (v, 0) (v, 0)
    have hz : z ∈ N.cylinderDomain := N.coordinate_inverse_mem x hx
    have hq : (q, a) ∈ N'.cylinderDomain := ⟨mem_univ _, ha⟩
    have hu : u.1 = 0 := by
      have h := N.sphereSlice_projection_mfderiv N' ha q hx v
      change A v = u.1 at h
      exact h.symm.trans hv
    have hmap : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u = w :=
      N.coordinate_map_mfderiv_inverse_prod hx w
    have hxmap : N.coordinate_map z = x := N.coordinate_map_coordinate_inverse hx
    have hX : 0 ≤ X := by
      change 0 ≤ EvolvingRoundCylinderMetric 0 z u u
      rw [← roundCylinderProductMetric_inner z u u]
      by_cases hu' : u = 0
      · simp [hu']
      · exact (roundCylinderProductMetric.pos z u hu').le
    have hY : 0 ≤ Y := by
      change 0 ≤ EvolvingRoundCylinderMetric 0 (q, a) (v, 0) (v, 0)
      rw [← roundCylinderProductMetric_inner (q, a) (v, 0) (v, 0)]
      by_cases hv' : (v, (0 : ℝ)) = (0 : RoundCylinderTangent (q, a))
      · simp [hv']
      · exact (roundCylinderProductMetric.pos (q, a) (v, 0) hv').le
    have hmetricN := (N.pullback_metric_bounds hz.2 u).1
    change (1 - N.epsilon) * N.scale ^ 2 * X ≤
      g.inner (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u) at hmetricN
    rw [hmap, hxmap] at hmetricN
    have hmetricN' := (N'.pullback_metric_bounds hq.2 (v, 0)).2
    change g.inner x w w ≤ (1 + N'.epsilon) * N'.scale ^ 2 * Y at hmetricN'
    have hlo : (199 / 200 : ℝ) * N.scale ^ 2 * X ≤ g.inner x w w := by
      nlinarith [mul_le_mul_of_nonneg_right hε (mul_nonneg (sq_nonneg N.scale) hX)]
    have hhi : g.inner x w w ≤ (201 / 200 : ℝ) * N'.scale ^ 2 * Y := by
      nlinarith [mul_le_mul_of_nonneg_right hε' (mul_nonneg (sq_nonneg N'.scale) hY)]
    have hricciN := N.ricci_quadratic_control_of_epsilon_le D hε z hz u
    rw [hmap, hxmap] at hricciN
    have haxial : X = u.2 ^ 2 := by
      simp [X, EvolvingRoundCylinderMetric, hu, pow_two]
    have hRhi : D.ricci x w w ≤ (7 / 50 : ℝ) * X := by
      change |D.ricci x w w - (1 / 2 : ℝ) * (X - u.2 ^ 2)| ≤
        (7 / 50 : ℝ) * X at hricciN
      rw [sub_eq_zero.mpr haxial, mul_zero, sub_zero] at hricciN
      exact (le_abs_self _).trans hricciN
    have hricciN' := N'.ricci_quadratic_control_of_epsilon_le D hε' (q, a) hq (v, 0)
    change |D.ricci x w w - (1 / 2 : ℝ) * (Y - (0 : ℝ) ^ 2)| ≤
      (7 / 50 : ℝ) * Y at hricciN'
    have hRlo : (9 / 25 : ℝ) * Y ≤ D.ricci x w w := by
      have h := (abs_le.mp hricciN').1
      norm_num at h
      linarith
    have hYzero : Y = 0 := zero_of_fixed_metric_ricci_bounds N.scale_pos
      hscale hY hlo hhi hRlo hRhi
    by_contra hvne
    have hvne' : (v, (0 : ℝ)) ≠ (0 : RoundCylinderTangent (q, a)) := by
      intro hh
      exact hvne (congrArg Prod.fst hh)
    have hp := roundCylinderProductMetric.pos (q, a) (v, 0) hvne'
    exact hp.ne' ((roundCylinderProductMetric_inner (q, a) (v, 0) (v, 0)).trans hYzero)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) q) := by
    unfold TangentSpace
    infer_instance
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

theorem sphereSlice_projection_diffeomorph_of_epsilon_le
    (N N' : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 200)
    (hε' : N'.epsilon ≤ 1 / 200) {a : ℝ}
    (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hmem : ∀ q : UnitTwoSphere, N'.coordinate_map (q, a) ∈ N.carrier) :
    ∃ e : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
      ∀ q : UnitTwoSphere,
        e q = (N.coordinate_inverse (N'.coordinate_map (q, a))).1 := by
  let f : UnitTwoSphere → UnitTwoSphere :=
    fun q => (N.coordinate_inverse (N'.coordinate_map (q, a))).1
  have hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f := by
    have hc : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere => N.coordinate_inverse (N'.coordinate_map (q, a))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hmem q))).comp q (N'.sphereSlice_contMDiff ha q)
    exact contMDiff_fst.comp hc
  have hlocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ f := by
    apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hf
    intro q
    exact N.sphereSlice_projection_mfderiv_bijective_of_epsilon_le N' hε hε' ha q (hmem q)
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  have hcover := isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph
  have hbij := Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected hcover
  exact ⟨hlocal.diffeomorphOfBijective hbij, fun _ => rfl⟩

end PoincareConjecture.EpsilonNeck
