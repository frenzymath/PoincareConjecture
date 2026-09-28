import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSliceProjection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalSphereContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle NNReal

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem abs_transition_slice_sub_le_of_scale_le_two_m28 (N N' : EpsilonNeck g)
    {a : ℝ} (ha : a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hmem : ∀ q : UnitTwoSphere, N'.coordinate_map (q, a) ∈ N.carrier)
    (hscale : N'.scale ≤ 2 * N.scale) (q r : UnitTwoSphere) :
    |(N.coordinate_inverse (N'.coordinate_map (q, a))).2 -
      (N.coordinate_inverse (N'.coordinate_map (r, a))).2| ≤ 5 * Real.pi := by
  let f : UnitTwoSphere → ℝ :=
    fun p => (N.coordinate_inverse (N'.coordinate_map (p, a))).2
  have hcoord (p : UnitTwoSphere) :=
    N'.coordinate_map_smooth.contMDiffAt
      (N'.cylinderDomain_open.mem_nhds (show (p, a) ∈ N'.cylinderDomain from
        ⟨mem_univ _, ha⟩))
  have hinv (p : UnitTwoSphere) := N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds (hmem p))
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f := by
    intro p
    exact contMDiffAt_snd.comp p ((hinv p).comp p
      ((hcoord p).comp p (contMDiffAt_id.prodMk contMDiffAt_const)))
  have hbound (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p) :
      |mvfderiv (𝓡 2) f p v| ≤ (5 : ℝ) * (roundSphereMetric 2).tangentNorm p v := by
    let x := N'.coordinate_map (p, a)
    let z := N.coordinate_inverse x
    let w := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map (p, a) (v, 0)
    let u := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
    let X := EvolvingRoundCylinderMetric 0 z u u
    let Y := (roundSphereMetric 2).inner p v v
    have hderiv : mvfderiv (𝓡 2) f p v = u.2 := by
      have hpair := (hasMFDerivAt_id (I := 𝓡 2) p).prodMk
        (hasMFDerivAt_const (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) a p)
      have hh := (hinv p).mdifferentiableAt (by simp)
      have hm := (hcoord p).mdifferentiableAt (by simp)
      have hcomp := hh.hasMFDerivAt.comp p (hm.hasMFDerivAt.comp p hpair)
      have hsnd := (hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
        (N.coordinate_inverse x)).comp p hcomp
      exact congrArg (fun L => L v) hsnd.mfderiv
    have hY : 0 ≤ Y := by
      by_cases hv : v = 0
      · simp [Y, hv]
      · exact ((roundSphereMetric 2).pos p v hv).le
    have hZ : u.2 ^ 2 ≤ X := by
      have hhor : 0 ≤ inner ℝ
          (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) z.1 u.1)
          (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) z.1 u.1) :=
        real_inner_self_nonneg
      dsimp [X, EvolvingRoundCylinderMetric]
      nlinarith
    have hX : 0 ≤ X := (sq_nonneg u.2).trans hZ
    have hmap := N.coordinate_map_mfderiv_inverse_prod (hmem p) w
    have hz := N.coordinate_inverse_mem x (hmem p)
    have hlow := (N.pullback_metric_bounds hz.2 u).1
    change (1 - N.epsilon) * N.scale ^ 2 * X ≤
      g.inner (N.coordinate_map z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z u) at hlow
    rw [hmap, N.coordinate_map_coordinate_inverse (hmem p)] at hlow
    have hhigh := (N'.pullback_metric_bounds (z := (p, a)) ha (v, 0)).2
    have hhorizontal : EvolvingRoundCylinderMetric 0 (p, a) (v, 0) (v, 0) = 2 * Y := by
      simp only [Y, EvolvingRoundCylinderMetric, roundSphereMetric_inner,
        RiemannianMetric.euclideanMetric_inner, sub_zero, mul_one, zero_mul, add_zero]
    change g.inner x w w ≤ (1 + N'.epsilon) * N'.scale ^ 2 *
      EvolvingRoundCylinderMetric 0 (p, a) (v, 0) (v, 0) at hhigh
    rw [hhorizontal] at hhigh
    have hlo : N.scale ^ 2 / 2 * X ≤ g.inner x w w := by
      nlinarith [mul_nonneg (sq_nonneg N.scale) hX,
        mul_nonneg (sub_nonneg.mpr N.epsilon_lt_half.le)
          (mul_nonneg (sq_nonneg N.scale) hX)]
    have hhi : g.inner x w w ≤ 3 * N'.scale ^ 2 * Y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr N'.epsilon_lt_half.le)
        (mul_nonneg (sq_nonneg N'.scale) hY)]
    have hsquares : N'.scale ^ 2 ≤ 4 * N.scale ^ 2 := by
      nlinarith [N.scale_pos, N'.scale_pos]
    have hXY : X ≤ 24 * Y := by
      have hs : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
      have hscaleY := mul_le_mul_of_nonneg_right hsquares hY
      nlinarith
    rw [hderiv]
    change |u.2| ≤ 5 * Real.sqrt Y
    nlinarith [sq_abs u.2, Real.sq_sqrt hY, Real.sqrt_nonneg Y, abs_nonneg u.2]
  let : PreconnectedSpace (UnitSphere 2) :=
    inferInstanceAs (PreconnectedSpace UnitTwoSphere)
  have hdist := (roundSphereMetric 2).abs_sub_le_mul_toReal_edist_of_derivative_bound
    (hf.of_le (by simp)) (K := (5 : ℝ≥0)) (by norm_num) hbound q r
  have hpi : ((roundSphereMetric 2).edist q r).toReal ≤ Real.pi := by
    rw [roundSphereMetric_edist_eq_angle (by norm_num), ENNReal.toReal_ofReal
      (Real.arccos_nonneg _)]
    exact Real.arccos_le_pi _
  exact hdist.trans (by simpa using mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 5))

theorem exists_transition_slice_oscillation_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ {a : ℝ}, a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        (∀ q : UnitTwoSphere, N'.coordinate_map (q, a) ∈ N.carrier) →
        ∀ q r : UnitTwoSphere,
          |(N.coordinate_inverse (N'.coordinate_map (q, a))).2 -
            (N.coordinate_inverse (N'.coordinate_map (r, a))).2| ≤ 5 * Real.pi := by
  obtain ⟨ε₀, hε₀, hsmall, hscale⟩ := exists_scale_comparison_at_common_closure_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' a ha hmem q r
  have hs := (hscale N N' hN hN'
    ⟨N'.coordinate_map (q, a), subset_closure (hmem q),
      subset_closure (N'.coordinate_map_mem ⟨mem_univ _, ha⟩)⟩).2
  exact N.abs_transition_slice_sub_le_of_scale_le_two_m28 N' ha hmem
    (by linarith [N.scale_pos]) q r

end PoincareConjecture.EpsilonNeck
