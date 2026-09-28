import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem coordinate_product_mfderiv_left_inverse (N : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain) (v : RoundCylinderTangent z) :
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) = v := by
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds (N.coordinate_map_mem hz))).mdifferentiableAt (by simp)
  have heq : N.coordinate_inverse ∘ N.coordinate_map =ᶠ[𝓝 z] id := by
    filter_upwards [N.cylinderDomain_open.mem_nhds hz] with y hy
    exact N.coordinate_inverse_coordinate_map hy
  have hcomp := mfderiv_comp z hi hm
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact (congrArg (fun L => L v) hcomp).symm

theorem sphere_coordinate_mfderiv (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    mfderiv (𝓡 3) (𝓡 3) (fun y => (N.coordinate_inverse y).1.1) x v =
      mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (N.coordinate_inverse x).1
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v).1 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun p : UnitTwoSphere => p.1) (N.coordinate_inverse x).1 :=
    (contMDiff_coe_sphere (n := 2) (m := ∞) (N.coordinate_inverse x).1).mdifferentiableAt (by simp)
  change mfderiv (𝓡 3) (𝓡 3)
    ((fun p : UnitTwoSphere => p.1) ∘ (Prod.fst ∘ N.coordinate_inverse)) x v = _
  rw [mfderiv_comp_apply x hc (mdifferentiableAt_fst.comp x hi),
    mfderiv_comp_apply x mdifferentiableAt_fst hi, mfderiv_fst]
  rfl

theorem sphere_coordinate_mfderiv_norm_le [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
        (mfderiv (𝓡 3) (𝓡 3) (fun y => (N.coordinate_inverse y).1.1) x v) ≤
      N.scale⁻¹ * g.tangentNorm x v := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let z := N.coordinate_inverse x
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v
  let w0 : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z.1 w.1
  have hmodel : EvolvingRoundCylinderMetric 0 z w w = 2 * ‖w0‖ ^ 2 + w.2 ^ 2 := by
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one]
    change 2 * inner ℝ w0 w0 + w.2 * w.2 = 2 * ‖w0‖ ^ 2 + w.2 ^ 2
    rw [real_inner_self_eq_norm_sq, pow_two w.2]
  have herr := N.normalized_pullback_quadratic_error (N.coordinate_inverse_mem x hx).2 w
  change |N.normalized_pullback z w w - EvolvingRoundCylinderMetric 0 z w w| ≤
    N.epsilon * EvolvingRoundCylinderMetric 0 z w w at herr
  rw [hmodel, N.normalized_pullback_inverse_tangent hx] at herr
  have hsq : ‖w0‖ ^ 2 ≤ N.scale⁻¹ ^ 2 * g.inner x v v := by
    have hhalf := N.epsilon_lt_half
    have hB : 0 ≤ 2 * ‖w0‖ ^ 2 + w.2 ^ 2 := by positivity
    have hmul := mul_nonneg (show 0 ≤ 1 / 2 - N.epsilon by linarith) hB
    nlinarith [(abs_le.mp herr).1, sq_nonneg w.2]
  have hvnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hnormsq : (N.scale⁻¹ * g.tangentNorm x v) ^ 2 =
      N.scale⁻¹ ^ 2 * g.inner x v v := by
    rw [mul_pow, RiemannianMetric.tangentNorm, Real.sq_sqrt hvnonneg]
  rw [N.sphere_coordinate_mfderiv hx v]
  change ‖w0‖ ≤ N.scale⁻¹ * g.tangentNorm x v
  have hnonneg : 0 ≤ N.scale⁻¹ * g.tangentNorm x v :=
    mul_nonneg (inv_nonneg.mpr N.scale_pos.le) (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg w0]

theorem sphere_coordinate_mfderiv_axis (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) :
    mfderiv (𝓡 3) (𝓡 3) (fun y => (N.coordinate_inverse y).1.1) x
      (N.normalizedAxialVector x) = 0 := by
  have hz := N.coordinate_inverse_mem x hx
  let C : M → (EuclideanSpace ℝ (Fin 3) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
    fun y => mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse y
  let a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) (N.coordinate_inverse x) := (0, 1)
  let b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) (N.coordinate_inverse x) := (0, 1)
  let d : EuclideanSpace ℝ (Fin 3) :=
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map
      (N.coordinate_inverse x) a
  have hleft := N.coordinate_product_mfderiv_left_inverse hz a
  change C (N.coordinate_map (N.coordinate_inverse x))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map
        (N.coordinate_inverse x) a) = b at hleft
  rw [N.coordinate_map_coordinate_inverse hx] at hleft
  have hinv : C x (N.normalizedAxialVector x) = N.scale⁻¹ • (0, 1) := by
    have hscaled : C x (N.scale⁻¹ • d) = N.scale⁻¹ • b := by
      rw [map_smul]
      exact congrArg (fun w => N.scale⁻¹ • w) hleft
    simpa only [normalizedAxialVector, a, d, b] using hscaled
  rw [N.sphere_coordinate_mfderiv hx]
  change mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1)
    (N.coordinate_inverse x).1 (C x (N.normalizedAxialVector x)).1 = 0
  rw [hinv]
  simp

theorem differentiableAt_transition_sphere_axial (N N' : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
    (hx' : N.coordinate_map z ∈ N'.carrier) :
    DifferentiableAt ℝ
      (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).1.1) z.2 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hc : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : UnitTwoSphere => p.1) :=
    contMDiff_coe_sphere (n := 2) (m := ∞)
  have hm := N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds hz)
  have hi := N'.coordinate_inverse_smooth.contMDiffAt (N'.carrier_open.mem_nhds hx')
  have hp : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (z.1, s)) z.2 := contMDiffAt_const.prodMk contMDiffAt_id
  exact mdifferentiableAt_iff_differentiableAt.mp
    ((hc.contMDiffAt.comp z.2
      (contMDiffAt_fst.comp z.2 (hi.comp z.2 (hm.comp z.2 hp)))).mdifferentiableAt (by simp))

theorem transition_sphere_axial_deriv (N N' : EpsilonNeck g)
    {z : RoundCylinderSpace} (hz : z ∈ N.cylinderDomain)
    (hx' : N.coordinate_map z ∈ N'.carrier) :
    deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).1.1) z.2 =
      N.scale • mfderiv (𝓡 3) (𝓡 3) (fun y => (N'.coordinate_inverse y).1.1)
        (N.coordinate_map z) (N.normalizedAxialVector (N.coordinate_map z)) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : UnitTwoSphere => p.1) :=
    contMDiff_coe_sphere (n := 2) (m := ∞)
  let D : RoundCylinderSpace → (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    fun w => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map w
  let L := mfderiv (𝓡 3) (𝓡 3) (fun y => (N'.coordinate_inverse y).1.1)
    (N.coordinate_map z)
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds hx')).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt (𝓡 3) (𝓡 3)
      (fun y => (N'.coordinate_inverse y).1.1) (N.coordinate_map z) :=
    (hcoe.contMDiffAt.mdifferentiableAt (by simp)).comp _
      (mdifferentiableAt_fst.comp _ hi)
  have hp : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun s : ℝ => (z.1, s)) z.2 := mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hd : deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).1.1) z.2 =
      L (D z (0, 1)) := by
    have hc := mfderiv_comp_apply z.2 hl (hm.comp z.2 hp) (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hc
    change deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).1.1) z.2 =
      L (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
        (N.coordinate_map ∘ (fun s : ℝ => (z.1, s))) z.2 1) at hc
    rw [mfderiv_comp_apply z.2 hm hp, mfderiv_prod_right] at hc
    exact hc
  rw [hd]
  change L (D z (0, 1)) = N.scale • L (N.scale⁻¹ •
    D (N.coordinate_inverse (N.coordinate_map z)) (0, 1))
  rw [N.coordinate_inverse_coordinate_map hz, map_smul, smul_smul,
    mul_inv_cancel₀ N.scale_pos.ne', one_smul]

theorem exists_intersecting_transition_sphere_axial_bound {η : ℝ} (hη : 0 < η) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ z ∈ N.cylinderDomain, N.coordinate_map z ∈ N'.carrier →
        ‖deriv (fun s => (N'.coordinate_inverse (N.coordinate_map (z.1, s))).1.1) z.2‖ < η := by
  obtain ⟨εa, hapos, hacap, haxis⟩ :=
    exists_intersecting_axial_control.{u} (α := η / 4) (by positivity)
  obtain ⟨εs, hspos, _, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1) (by norm_num)
  refine ⟨min εa εs, lt_min hapos hspos, (min_le_left _ _).trans hacap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' z hz hx'
  let x := N.coordinate_map z
  have hx : x ∈ N.carrier := N.coordinate_map_mem hz
  obtain ⟨σ, _, hclose⟩ := haxis N' N (hN'.trans (min_le_left _ _))
    (hN.trans (min_le_left _ _)) x hx' hx
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (fun y => (N'.coordinate_inverse y).1.1) x
  have hzero : L (N'.normalizedAxialVector x) = 0 :=
    N'.sphere_coordinate_mfderiv_axis hx'
  have hnorm : ‖L (N.normalizedAxialVector x)‖ < N'.scale⁻¹ * (η / 4) := by
    have hb := N'.sphere_coordinate_mfderiv_norm_le hx'
      (N.normalizedAxialVector x - σ • N'.normalizedAxialVector x)
    change ‖L (N.normalizedAxialVector x - σ • N'.normalizedAxialVector x)‖ ≤ _ at hb
    rw [map_sub, map_smul, hzero, smul_zero, sub_zero] at hb
    exact hb.trans_lt (mul_lt_mul_of_pos_left hclose (inv_pos.mpr N'.scale_pos))
  have hr := (hscale N' N (hN'.trans (min_le_right _ _))
    (hN.trans (min_le_right _ _)) ⟨x, hx', hx⟩).2
  have hratio : N.scale / N'.scale ≤ 2 := by linarith [(abs_lt.mp hr).2]
  rw [N.transition_sphere_axial_deriv N' hz hx', norm_smul,
    Real.norm_eq_abs, abs_of_pos N.scale_pos]
  calc
    N.scale * ‖L (N.normalizedAxialVector x)‖ <
        N.scale * (N'.scale⁻¹ * (η / 4)) := mul_lt_mul_of_pos_left hnorm N.scale_pos
    _ = (N.scale / N'.scale) * (η / 4) := by rw [div_eq_mul_inv]; ring
    _ ≤ 2 * (η / 4) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ < η := by linarith

end PoincareConjecture.EpsilonNeck
