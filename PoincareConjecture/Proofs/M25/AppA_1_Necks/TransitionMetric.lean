import PoincareConjecture.Proofs.M25.AppA_1_Necks.TransitionHeight
import PoincareConjecture.Proofs.M25.Mathlib.SphereQuadraticComparison












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}




theorem normalized_pullback_inverse_tangent (N : EpsilonNeck g)
    {x : M} (hx : x ∈ N.carrier) (v : TangentSpace (𝓡 3) x) :
    N.normalized_pullback (N.coordinate_inverse x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x v) =
      N.scale⁻¹ ^ 2 * g.inner x v v := by
  simp only [normalized_pullback, roundCylinderPullback,
    N.coordinate_product_mfderiv_right_inverse hx v]
  exact congrArg (fun y : M => N.scale⁻¹ ^ 2 * g.inner y v v)
    (N.coordinate_map_coordinate_inverse hx)





theorem normalized_pullback_transition (N N' : EpsilonNeck g)
    {z : RoundCylinderSpace} (hx' : N.coordinate_map z ∈ N'.carrier)
    (v : RoundCylinderTangent z) :
    let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N'.coordinate_inverse
      (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
    N'.normalized_pullback (N'.coordinate_inverse (N.coordinate_map z)) w w =
      (N.scale / N'.scale) ^ 2 * N.normalized_pullback z v v := by
  dsimp only
  rw [N'.normalized_pullback_inverse_tangent hx']
  simp only [normalized_pullback, roundCylinderPullback]
  field_simp [N.scale_pos.ne', N'.scale_pos.ne']




theorem transition_slice_mfderiv_components (N N' : EpsilonNeck g)
    {q : UnitTwoSphere} {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hx' : N.coordinate_map (q, s) ∈ N'.carrier) (v : TangentSpace (𝓡 2) q) :
    let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N'.coordinate_inverse
      (N.coordinate_map (q, s))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) (v, 0))
    mfderiv (𝓡 2) (𝓡 2)
      (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).1) q v =
        w.1 ∧
      mvfderiv (𝓡 2)
        (fun p : UnitTwoSphere => (N'.coordinate_inverse (N.coordinate_map (p, s))).2) q v =
        w.2 := by
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds
      (show (q, s) ∈ N.cylinderDomain from ⟨mem_univ q, hs⟩))).mdifferentiableAt (by simp)
  have hi := (N'.coordinate_inverse_smooth.contMDiffAt
    (N'.carrier_open.mem_nhds hx')).mdifferentiableAt (by simp)
  have hp : MDifferentiableAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun p : UnitTwoSphere => (p, s)) q :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  constructor
  · change (mfderiv (𝓡 2) (𝓡 2)
      (Prod.fst ∘ (N'.coordinate_inverse ∘
        (N.coordinate_map ∘ (fun p : UnitTwoSphere => (p, s))))) q) v = _
    rw [mfderiv_comp q mdifferentiableAt_fst (hi.comp q (hm.comp q hp)),
      mfderiv_comp q hi (hm.comp q hp), mfderiv_comp q hm hp,
      mfderiv_prod_left, mfderiv_fst]
    rfl
  · change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (Prod.snd ∘ (N'.coordinate_inverse ∘
        (N.coordinate_map ∘ (fun p : UnitTwoSphere => (p, s))))) q) v = _
    rw [mfderiv_comp q mdifferentiableAt_snd (hi.comp q (hm.comp q hp)),
      mfderiv_comp q hi (hm.comp q hp), mfderiv_comp q hm hp,
      mfderiv_prod_left, mfderiv_snd]
    rfl






theorem exists_intersecting_transition_sphere_norm_bounds {K : ℝ} (hK : 1 < K) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      ∀ z ∈ N.cylinderDomain, N.coordinate_map z ∈ N'.carrier →
      ∀ v : TangentSpace (𝓡 2) z.1,
        let F : UnitTwoSphere → UnitTwoSphere :=
          fun q => (N'.coordinate_inverse (N.coordinate_map (q, z.2))).1
        let V := (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
          (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z.1 v)
        let W := (norm : EuclideanSpace ℝ (Fin 3) → ℝ)
          (mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) (F z.1)
            (mfderiv (𝓡 2) (𝓡 2) F z.1 v))
        K⁻¹ * V ≤ W ∧ W ≤ K * V := by
  obtain ⟨d, hd, hlo, hup⟩ := Real.exists_quadratic_component_tolerance hK
  obtain ⟨εs, hspos, hscap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := d) hd.1
  obtain ⟨εh, hhpos, _, hheight⟩ :=
    exists_intersecting_transition_height_horizontal_bound.{u} (α := d) hd.1
  refine ⟨min εs (min εh d), lt_min hspos (lt_min hhpos hd.1),
    (min_le_left _ _).trans hscap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' z hz hx' v
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  have hNs : N.epsilon ≤ εs := hN.trans (min_le_left _ _)
  have hN's : N'.epsilon ≤ εs := hN'.trans (min_le_left _ _)
  have hNh : N.epsilon ≤ εh := (hN.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hN'h : N'.epsilon ≤ εh := (hN'.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hNd : N.epsilon ≤ d := (hN.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hN'd : N'.epsilon ≤ d := (hN'.trans (min_le_right _ _)).trans (min_le_right _ _)
  let z' := N'.coordinate_inverse (N.coordinate_map z)
  let w := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N'.coordinate_inverse
    (N.coordinate_map z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (v, 0))
  let v0 : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z.1 v
  let w0 : EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 2) (𝓡 3) (fun p : UnitTwoSphere => p.1) z'.1 w.1
  let V := ‖v0‖
  let W := ‖w0‖
  let a := N.normalized_pullback z (v, 0) (v, 0)
  let b := N'.normalized_pullback z' w w
  have hparts := N.transition_slice_mfderiv_components N' hz.2 hx' v
  have hmodel : EvolvingRoundCylinderMetric 0 z (v, 0) (v, 0) = 2 * V ^ 2 := by
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one, zero_mul, add_zero]
    change 2 * inner ℝ v0 v0 = 2 * ‖v0‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  have hmodel' : EvolvingRoundCylinderMetric 0 z' w w = 2 * W ^ 2 + w.2 ^ 2 := by
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one]
    change 2 * inner ℝ w0 w0 + w.2 * w.2 = 2 * ‖w0‖ ^ 2 + w.2 ^ 2
    rw [real_inner_self_eq_norm_sq, pow_two w.2]
  have ha : |a - 2 * V ^ 2| ≤ N.epsilon * (2 * V ^ 2) := by
    simpa only [hmodel] using N.normalized_pullback_quadratic_error hz.2 (v, 0)
  have hb : |b - (2 * W ^ 2 + w.2 ^ 2)| ≤ N'.epsilon * (2 * W ^ 2 + w.2 ^ 2) := by
    have hb' := N'.normalized_pullback_quadratic_error (N'.coordinate_inverse_mem _ hx').2 w
    change |b - EvolvingRoundCylinderMetric 0 z' w w| ≤
      N'.epsilon * EvolvingRoundCylinderMetric 0 z' w w at hb'
    rwa [hmodel'] at hb'
  have hmetric : b = (N.scale / N'.scale) ^ 2 * a :=
    N.normalized_pullback_transition N' hx' (v, 0)
  have hratio := (hscale N' N hN's hNs
    ⟨N.coordinate_map z, hx', N.coordinate_map_mem hz⟩).2
  have hr : N.scale / N'.scale ∈ Icc (1 - d) (1 + d) := by
    constructor <;> linarith [(abs_lt.mp hratio).1, (abs_lt.mp hratio).2]
  have ht : |w.2| ≤ d * V := by
    have ht' := hheight N N' hNh hN'h z hz hx' v
    rw [hparts.2] at ht'
    exact ht'
  have hbound := Real.quadratic_component_norm_bounds hK hd hlo hup hNd hN'd hr
    (norm_nonneg _) (norm_nonneg _) ha hb hmetric ht
  dsimp only
  rw [hparts.1]
  exact hbound

end PoincareConjecture.EpsilonNeck
