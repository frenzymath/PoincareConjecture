import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

private theorem zero_of_metric_ricci_bounds {s t X Y G R : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hscale : t ≤ 2 * s) (hY : 0 ≤ Y)
    (hlo : s ^ 2 / 2 * X ≤ G) (hhi : G ≤ (3 / 2 : ℝ) * t ^ 2 * Y)
    (hRlo : (49 / 100 : ℝ) * Y ≤ R) (hRhi : R ≤ (1 / 100 : ℝ) * X) : Y = 0 := by
  have hts : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  have hcomp : s ^ 2 / 2 * X ≤ 6 * s ^ 2 * Y := by
    nlinarith [mul_le_mul_of_nonneg_right hts hY]
  have hXY : X ≤ 12 * Y := by
    have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
    nlinarith
  linarith

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem coordinate_map_mfderiv_inverse_prod {x : M} (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) = v := by
  have hh := mfderiv_comp x
    ((N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds (N.coordinate_inverse_mem x hx))).mdifferentiableAt
      (by simp))
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp))
  have heq : N.coordinate_map ∘ N.coordinate_inverse =ᶠ[𝓝 x] id := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.coordinate_map_coordinate_inverse hy
  rw [heq.mfderiv_eq, mfderiv_id] at hh
  exact (congrArg (fun L => L v) hh).symm

theorem sphereSlice_contMDiff {a : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : UnitTwoSphere => N.coordinate_map (p, a)) := by
  intro p
  exact (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds ⟨mem_univ _, ha⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)

theorem sphereSlice_mfderiv {a : ℝ} (ha : a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => N.coordinate_map (p, a)) q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, a) (v, 0) := by
  have hz : (q, a) ∈ N.cylinderDomain := ⟨mem_univ _, ha⟩
  have hc := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hs : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, a)) q :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  change mfderiv (𝓡 2) (𝓡 3)
    (N.coordinate_map ∘ (fun p : UnitTwoSphere => (p, a))) q v = _
  have hd := ((hasMFDerivAt_id (I := 𝓡 2) q).prodMk
    (hasMFDerivAt_const (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) a q)).mfderiv
  rw [mfderiv_comp q hc hs]
  simp only [id_eq] at hd
  rw [hd]
  rfl

theorem centralSphere_mfderiv (q : UnitTwoSphere) (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => N.coordinate_map (p, 0)) q v =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, 0) (v, 0) :=
  N.sphereSlice_mfderiv
    (by constructor <;> linarith [inv_pos.mpr N.epsilon_pos]) q v

theorem sphereSlice_projection_mfderiv (N' : EpsilonNeck g) {a : ℝ}
    (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹) (q : UnitTwoSphere)
    (hx : N'.coordinate_map (q, a) ∈ N.carrier) (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse
        (N'.coordinate_map (q, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, a) (v, 0))).1 := by
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hs := (N'.sphereSlice_contMDiff ha).mdifferentiableAt (by simp) (x := q)
  change mfderiv (𝓡 2) (𝓡 2)
    (Prod.fst ∘ (N.coordinate_inverse ∘ (fun p : UnitTwoSphere => N'.coordinate_map (p, a)))) q v = _
  rw [mfderiv_comp q mdifferentiableAt_fst (hi.comp q hs),
    mfderiv_comp q hi hs, mfderiv_fst]
  change (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse _
    (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => N'.coordinate_map (p, a)) q v)).1 = _
  rw [N'.sphereSlice_mfderiv ha]

theorem centralSphere_projection_mfderiv (N' : EpsilonNeck g) (q : UnitTwoSphere)
    (hx : N'.coordinate_map (q, 0) ∈ N.carrier) (v : TangentSpace (𝓡 2) q) :
    mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, 0))).1) q v =
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse
        (N'.coordinate_map (q, 0))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (q, 0) (v, 0))).1 :=
  N.sphereSlice_projection_mfderiv N'
    (by constructor <;> linarith [inv_pos.mpr N'.epsilon_pos]) q hx v

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem sphereSlice_projection_mfderiv_bijective_of_ricci_error
    (D : LeviCivitaData g) (N' : EpsilonNeck g) {a : ℝ}
    (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹) (q : UnitTwoSphere)
    (hx : N'.coordinate_map (q, a) ∈ N.carrier) (hscale : N'.scale ≤ 2 * N.scale)
    (hN : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      |D.ricci (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) -
        (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v)
    (hN' : ∀ z ∈ N'.cylinderDomain, ∀ v : RoundCylinderTangent z,
      |D.ricci (N'.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z v) -
        (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v) :
    Function.Bijective (mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q) := by
  let A := mfderiv (𝓡 2) (𝓡 2)
    (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, a))).1) q
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
    have hlo : N.scale ^ 2 / 2 * X ≤ g.inner x w w := by
      nlinarith [mul_nonneg (sq_nonneg N.scale) hX,
        mul_nonneg (sub_nonneg.mpr N.epsilon_lt_half.le)
          (mul_nonneg (sq_nonneg N.scale) hX)]
    have hhi : g.inner x w w ≤ (3 / 2 : ℝ) * N'.scale ^ 2 * Y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr N'.epsilon_lt_half.le)
        (mul_nonneg (sq_nonneg N'.scale) hY)]
    have hricciN := hN z hz u
    rw [hmap, hxmap] at hricciN
    have haxial : X = u.2 ^ 2 := by
      simp [X, EvolvingRoundCylinderMetric, hu, pow_two]
    have hRhi : D.ricci x w w ≤ (1 / 100 : ℝ) * X := by
      change |D.ricci x w w - (1 / 2 : ℝ) * (X - u.2 ^ 2)| ≤
        (1 / 100 : ℝ) * X at hricciN
      have hmodel : X - u.2 ^ 2 = 0 := sub_eq_zero.mpr haxial
      rw [hmodel, mul_zero, sub_zero] at hricciN
      exact (le_abs_self _).trans hricciN
    have hricciN' := hN' (q, a) hq (v, 0)
    change |D.ricci x w w - (1 / 2 : ℝ) * (Y - (0 : ℝ) ^ 2)| ≤
      (1 / 100 : ℝ) * Y at hricciN'
    have hRlo : (49 / 100 : ℝ) * Y ≤ D.ricci x w w := by
      have h := (abs_le.mp hricciN').1
      norm_num at h
      linarith
    have hYzero : Y = 0 := zero_of_metric_ricci_bounds N.scale_pos N'.scale_pos
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

theorem centralSphere_projection_mfderiv_bijective_of_ricci_error
    (D : LeviCivitaData g) (N' : EpsilonNeck g) (q : UnitTwoSphere)
    (hx : N'.coordinate_map (q, 0) ∈ N.carrier) (hscale : N'.scale ≤ 2 * N.scale)
    (hN : ∀ z ∈ N.cylinderDomain, ∀ v : RoundCylinderTangent z,
      |D.ricci (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) -
        (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v)
    (hN' : ∀ z ∈ N'.cylinderDomain, ∀ v : RoundCylinderTangent z,
      |D.ricci (N'.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z v) -
        (1 / 2 : ℝ) * (EvolvingRoundCylinderMetric 0 z v v - v.2 ^ 2)| ≤
          (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z v v) :
    Function.Bijective (mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N.coordinate_inverse (N'.coordinate_map (p, 0))).1) q) :=
  N.sphereSlice_projection_mfderiv_bijective_of_ricci_error D N'
    (by constructor <;> linarith [inv_pos.mpr N'.epsilon_pos]) q hx hscale hN hN'

end PoincareConjecture.EpsilonNeck
