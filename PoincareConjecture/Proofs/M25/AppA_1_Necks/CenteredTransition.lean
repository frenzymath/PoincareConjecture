import PoincareConjecture.Proofs.M25.AppA_1_Necks.ChristoffelControl
import PoincareConjecture.Proofs.M25.AppA_1_Necks.Overlap_A11
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.Hessian











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}



noncomputable def centeredEuclideanTransition (N N' : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (q' : UnitTwoSphere) (s' : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  let z := N'.coordinate_inverse (N.euclideanParametrization q s x)
  (RiemannianMetric.lineModelEquiv 2)
    (chartAt (EuclideanSpace ℝ (Fin 2)) q' z.1, z.2 - s')



theorem centeredEuclideanTransition_zero (N N' : EpsilonNeck g)
    (q q' : UnitTwoSphere) {s s' : ℝ}
    (hs' : s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N.coordinate_map (q, s) = N'.coordinate_map (q', s')) :
    N.centeredEuclideanTransition N' q s q' s' 0 = 0 := by
  simp only [centeredEuclideanTransition, euclideanParametrization_zero, hx,
    N'.coordinate_inverse_coordinate_map (show (q', s') ∈ N'.cylinderDomain from
      ⟨mem_univ _, hs'⟩),
    Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_center, sub_self]
  exact (RiemannianMetric.lineModelEquiv 2).map_zero



theorem centeredEuclideanTransition_germ (N N' : EpsilonNeck g)
    (q q' : UnitTwoSphere) {s s' : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hs' : s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N.coordinate_map (q, s) = N'.coordinate_map (q', s')) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U ∧ 0 ∈ U ∧
      ContDiffOn ℝ ∞ (N.centeredEuclideanTransition N' q s q' s') U ∧
      ∀ x ∈ U,
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
          Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
        N.euclideanParametrization q s x ∈ N'.carrier ∧
        (N'.coordinate_inverse (N.euclideanParametrization q s x)).1 ∈
          (chartAt (EuclideanSpace ℝ (Fin 2)) q').source ∧
        ((0, s') + (RiemannianMetric.lineModelEquiv 2).symm
          (N.centeredEuclideanTransition N' q s q' s' x)).2 ∈
            Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ ∧
        N'.euclideanParametrization q' s'
          (N.centeredEuclideanTransition N' q s q' s' x) =
            N.euclideanParametrization q s x := by
  let P := N.euclideanParametrization q s
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q'
  let U0 : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹}
  have hU0 : IsOpen U0 := isOpen_Ioo.preimage
    (continuous_snd.comp (continuous_const.add
      (RiemannianMetric.lineModelEquiv 2).symm.continuous))
  have hP : ContMDiffOn (𝓡 3) (𝓡 3) ∞ P U0 := fun x hx =>
    (N.euclideanParametrization_contMDiffAt q s hx).contMDiffWithinAt
  let V := N'.carrier ∩ N'.coordinate_inverse ⁻¹' (c.source ×ˢ univ)
  have hV : IsOpen V := N'.coordinate_inverse_smooth.continuousOn.isOpen_inter_preimage
    N'.carrier_open (c.open_source.prod isOpen_univ)
  let U := U0 ∩ P ⁻¹' V
  have hU : IsOpen U := hP.continuousOn.isOpen_inter_preimage hU0 hV
  have hZ0 : N'.coordinate_inverse (P 0) = (q', s') := by
    dsimp only [P]
    rw [euclideanParametrization_zero, hx,
      N'.coordinate_inverse_coordinate_map ⟨mem_univ _, hs'⟩]
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U := by
    refine ⟨?_, ?_, ?_⟩
    · change ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm
        (0 : EuclideanSpace ℝ (Fin 3))).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      simpa only [map_zero, add_zero] using hs
    · change N.euclideanParametrization q s 0 ∈ N'.carrier
      rw [euclideanParametrization_zero, hx]
      exact N'.coordinate_map_mem ⟨mem_univ _, hs'⟩
    · change N'.coordinate_inverse (P 0) ∈ c.source ×ˢ univ
      rw [hZ0]
      exact ⟨mem_chart_source _ _, mem_univ _⟩
  refine ⟨U, hU, h0, ?_, ?_⟩
  · intro x hxU
    have hi := (N'.coordinate_inverse_smooth.contMDiffAt
      (N'.carrier_open.mem_nhds hxU.2.1)).comp x
        (N.euclideanParametrization_contMDiffAt q s hxU.1)
    have hc := (contMDiffOn_chart (I := 𝓡 2) (n := (∞ : ℕ∞ω)) (x := q')).contMDiffAt
      (c.open_source.mem_nhds hxU.2.2.1)
    have hfst : ContDiffAt ℝ ∞
        (fun y => c (N'.coordinate_inverse (P y)).1) x :=
      contMDiffAt_iff_contDiffAt.mp (hc.comp x (contMDiffAt_fst.comp x hi))
    have hsnd : ContDiffAt ℝ ∞
        (fun y => (N'.coordinate_inverse (P y)).2) x :=
      contMDiffAt_iff_contDiffAt.mp (contMDiffAt_snd.comp x hi)
    exact ((RiemannianMetric.lineModelEquiv 2).contDiff.contDiffAt.comp x
      (hfst.prodMk (hsnd.sub contDiffAt_const))).contDiffWithinAt
  · intro x hxU
    have hphi : (0, s') + (RiemannianMetric.lineModelEquiv 2).symm
        (N.centeredEuclideanTransition N' q s q' s' x) =
        (c (N'.coordinate_inverse (P x)).1, (N'.coordinate_inverse (P x)).2) := by
      dsimp only [centeredEuclideanTransition, P, c]
      rw [ContinuousLinearEquiv.symm_apply_apply]
      ext <;> simp
    refine ⟨hxU.1, hxU.2.1, hxU.2.2.1, ?_, ?_⟩
    · rw [hphi]
      exact (N'.coordinate_inverse_mem _ hxU.2.1).2
    · rw [euclideanParametrization, hphi]
      change N'.coordinate_map
        (c.symm (c (N'.coordinate_inverse (P x)).1),
          (N'.coordinate_inverse (P x)).2) = P x
      rw [c.left_inv hxU.2.2.1]
      exact N'.coordinate_map_coordinate_inverse hxU.2.1



theorem normalizedEuclideanCoefficients_transition_eventuallyEq (N N' : EpsilonNeck g)
    (q q' : UnitTwoSphere) {s s' : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hs' : s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N.coordinate_map (q, s) = N'.coordinate_map (q', s')) :
    ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)), ∀ v w : EuclideanSpace ℝ (Fin 3),
      N.m25_normalizedEuclideanCoefficients q s x v w =
        (N'.scale / N.scale) ^ 2 * N'.m25_normalizedEuclideanCoefficients q' s'
          (N.centeredEuclideanTransition N' q s q' s' x)
          (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') x v)
          (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') x w) := by
  obtain ⟨U, hU, h0, hH, hret⟩ := N.centeredEuclideanTransition_germ N' q q' hs hs' hx
  filter_upwards [hU.mem_nhds h0] with x hxU
  intro v w
  have hr := hret x hxU
  have heq : N'.euclideanParametrization q' s' ∘
      N.centeredEuclideanTransition N' q s q' s' =ᶠ[𝓝 x]
        N.euclideanParametrization q s :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) (fun y hy => (hret y hy).2.2.2.2)
  have hd := g.pullbackCoefficients_comp_of_eventuallyEq
    ((N'.euclideanParametrization_contMDiffAt q' s' hr.2.2.2.1).mdifferentiableAt (by simp))
    ((hH.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)) heq v w
  rw [N.normalizedEuclideanCoefficients_pullback q s hr.1,
    N'.normalizedEuclideanCoefficients_pullback q' s' hr.2.2.2.1]
  change N.scale⁻¹ ^ 2 * g.pullbackCoefficients (N.euclideanParametrization q s) x v w =
    (N'.scale / N.scale) ^ 2 * (N'.scale⁻¹ ^ 2 *
      g.pullbackCoefficients (N'.euclideanParametrization q' s')
        (N.centeredEuclideanTransition N' q s q' s' x)
        (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') x v)
        (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') x w))
  rw [hd]
  field_simp [N.scale_pos.ne', N'.scale_pos.ne']

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem norm_fderiv_centeredEuclideanTransition_le (N N' : EpsilonNeck g)
    (q q' : UnitTwoSphere) {s s' : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hs' : s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N.coordinate_map (q, s) = N'.coordinate_map (q', s')) :
    ‖fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') 0‖ ≤
      3 * (N.scale / N'.scale) := by
  let ρ := N.scale / N'.scale
  let κ := (N'.scale / N.scale) ^ 2
  have hρ : 0 < ρ := div_pos N.scale_pos N'.scale_pos
  have hκ : 0 < κ := sq_pos_of_pos (div_pos N'.scale_pos N.scale_pos)
  have hcancel : ρ ^ 2 * κ = 1 := by
    dsimp [ρ, κ]
    field_simp [N.scale_pos.ne', N'.scale_pos.ne']
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  let D := fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') 0
  have hmetric := (N.normalizedEuclideanCoefficients_transition_eventuallyEq
    N' q q' hs hs' hx).self_of_nhds v v
  rw [N.centeredEuclideanTransition_zero N' q q' hs' hx] at hmetric
  have hsq : (1 / 2 : ℝ) * ‖D v‖ ^ 2 ≤ ρ ^ 2 * (3 * ‖v‖ ^ 2) := by
    calc
      _ = ρ ^ 2 * (κ * ((1 / 2 : ℝ) * ‖D v‖ ^ 2)) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ ρ ^ 2 * (κ * N'.m25_normalizedEuclideanCoefficients q' s' 0 (D v) (D v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (N'.normalizedEuclideanCoefficients_lower q' hs' (D v)) hκ.le) (sq_nonneg ρ)
      _ = ρ ^ 2 * N.m25_normalizedEuclideanCoefficients q s 0 v v := by rw [hmetric]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (N.normalizedEuclideanCoefficients_upper q hs v) (sq_nonneg ρ)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * ρ * ‖v‖)).mp
  nlinarith [sq_nonneg (ρ * ‖v‖)]



theorem exists_centeredEuclideanTransition_hessian_scaled_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g)
      (q q' : UnitTwoSphere) {s s' : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
      N.coordinate_map (q, s) = N'.coordinate_map (q', s') →
      ‖fderiv ℝ (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s')) 0‖ ≤
        K * ((N.scale / N'.scale) * N.epsilon +
          (N.scale / N'.scale) ^ 2 * N'.epsilon) := by
  obtain ⟨C, hC, hfirst⟩ := exists_normalizedEuclideanCoefficients_firstJet_bound.{u}
  refine ⟨27 * C, by positivity, ?_⟩
  intro M _ _ _ _ _ _ g N N' q q' s s' hs hs' hx
  let H := N.centeredEuclideanTransition N' q s q' s'
  let B := N.m25_normalizedEuclideanCoefficients q s
  let κ := (N'.scale / N.scale) ^ 2
  let A := fun y => κ • N'.m25_normalizedEuclideanCoefficients q' s' y
  let ρ := N.scale / N'.scale
  have hρ : 0 < ρ := div_pos N.scale_pos N'.scale_pos
  have hκ : 0 < κ := sq_pos_of_pos (div_pos N'.scale_pos N.scale_pos)
  have hH0 : H 0 = 0 := N.centeredEuclideanTransition_zero N' q q' hs' hx
  have hNpos := N.epsilon_pos
  have hN'pos := N'.epsilon_pos
  have hdiff (N0 : EpsilonNeck g) (q0 : UnitTwoSphere) {s0 : ℝ}
      (hs0 : s0 ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹) :
      DifferentiableAt ℝ (N0.m25_normalizedEuclideanCoefficients q0 s0) 0 :=
    (N0.m25_normalizedEuclideanCoefficients_contDiffAt q0 s0
      (by simpa only [map_zero, add_zero] using hs0)).differentiableAt (by simp)
  have hell (N0 : EpsilonNeck g) (q0 : UnitTwoSphere) {s0 : ℝ}
      (hs0 : s0 ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹) (l : ℝ) (hl : 0 < l)
      (v : EuclideanSpace ℝ (Fin 3)) :
      (l / 2) * ‖v‖ ^ 2 ≤ (l • N0.m25_normalizedEuclideanCoefficients q0 s0 0) v v := by
    change (l / 2) * ‖v‖ ^ 2 ≤ l * N0.m25_normalizedEuclideanCoefficients q0 s0 0 v v
    nlinarith [mul_le_mul_of_nonneg_left
      (N0.normalizedEuclideanCoefficients_lower q0 hs0 v) hl.le]
  have hGamma (N0 : EpsilonNeck g) (q0 : UnitTwoSphere) {s0 : ℝ}
      (hs0 : s0 ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹) (l : ℝ) (hl : 0 < l) :
      ‖CoordinateExponential.christoffelBilinear
        (fun y => l • N0.m25_normalizedEuclideanCoefficients q0 s0 y) 0‖ ≤
          3 * C * N0.epsilon := by
    have hder := ((hdiff N0 q0 hs0).hasFDerivAt.const_smul l).fderiv
    change fderiv ℝ (fun y => l • N0.m25_normalizedEuclideanCoefficients q0 s0 y) 0 =
      l • fderiv ℝ (N0.m25_normalizedEuclideanCoefficients q0 s0) 0 at hder
    have hest := CoordinateExponential.norm_christoffelBilinear_le_of_ellipticity
      (fun y => l • N0.m25_normalizedEuclideanCoefficients q0 s0 y) 0
      (a := l / 2) (by positivity) (hell N0 q0 hs0 l hl)
    rw [hder, norm_smul, Real.norm_eq_abs, abs_of_pos hl] at hest
    calc
      _ ≤ (3 / (2 * (l / 2))) *
          (l * ‖fderiv ℝ (N0.m25_normalizedEuclideanCoefficients q0 s0) 0‖) := hest
      _ = 3 * ‖fderiv ℝ (N0.m25_normalizedEuclideanCoefficients q0 s0) 0‖ := by
        field_simp [hl.ne']
      _ ≤ 3 * (C * N0.epsilon) :=
        mul_le_mul_of_nonneg_left (hfirst N0 q0 hs0) (by norm_num)
      _ = _ := by ring
  have hGB : ‖CoordinateExponential.christoffelBilinear B 0‖ ≤ 3 * C * N.epsilon := by
    simpa only [one_smul] using hGamma N q hs 1 zero_lt_one
  have hGA : ‖CoordinateExponential.christoffelBilinear A 0‖ ≤ 3 * C * N'.epsilon :=
    hGamma N' q' hs' κ hκ
  have hBdiff : DifferentiableAt ℝ B 0 := hdiff N q hs
  have hAdiff : DifferentiableAt ℝ A (H 0) := by
    rw [hH0]
    exact (hdiff N' q' hs').const_smul κ
  have hBinv : (B 0).IsInvertible :=
    CoordinateTransition.isInvertible_of_uniformEllipticity (a := 1 / 2)
      (by norm_num) (N.normalizedEuclideanCoefficients_lower q hs)
  have hAinv : (A (H 0)).IsInvertible := by
    rw [hH0]
    exact CoordinateTransition.isInvertible_of_uniformEllipticity (a := κ / 2)
      (by positivity) (hell N' q' hs' κ hκ)
  have hmetric : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)), ∀ v w,
      B y v w = A (H y) (fderiv ℝ H y v) (fderiv ℝ H y w) :=
    N.normalizedEuclideanCoefficients_transition_eventuallyEq N' q q' hs hs' hx
  have hsurj : Function.Surjective (fderiv ℝ H 0) :=
    CoordinateTransition.surjective_of_pullback_isInvertible hBinv hmetric.self_of_nhds
  obtain ⟨U, hU, h0, hH, _⟩ := N.centeredEuclideanTransition_germ N' q q' hs hs' hx
  have hBs : ∀ᶠ y in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)), ∀ v w, B y v w = B y w v :=
    Filter.Eventually.of_forall fun y v w => N.m25_normalizedEuclideanCoefficients_symm q s y v w
  have hAs : ∀ᶠ y in 𝓝 (H 0), ∀ v w, A y v w = A y w v :=
    Filter.Eventually.of_forall fun y v w => congrArg (κ * ·)
      (N'.m25_normalizedEuclideanCoefficients_symm q' s' y v w)
  have hD : ‖fderiv ℝ H 0‖ ≤ 3 * ρ :=
    N.norm_fderiv_centeredEuclideanTransition_le N' q q' hs hs' hx
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  have hess := CoordinateTransition.fderiv_fderiv_eq_christoffel hBdiff hAdiff hBinv hAinv
    hBs hAs (hH.contDiffAt (hU.mem_nhds h0)) hsurj hmetric v w
  rw [hH0] at hess
  rw [hess]
  have hDv (v : EuclideanSpace ℝ (Fin 3)) : ‖fderiv ℝ H 0 v‖ ≤ 3 * ρ * ‖v‖ :=
    ((fderiv ℝ H 0).le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  calc
    _ ≤ ‖fderiv ℝ H 0 (CoordinateExponential.christoffelBilinear B 0 v w)‖ +
        ‖CoordinateExponential.christoffelBilinear A 0
          (fderiv ℝ H 0 v) (fderiv ℝ H 0 w)‖ := norm_sub_le _ _
    _ ≤ (3 * ρ) * ((3 * C * N.epsilon) * ‖v‖ * ‖w‖) +
        (3 * C * N'.epsilon) * (3 * ρ * ‖v‖) * (3 * ρ * ‖w‖) := by
      apply add_le_add
      · apply (hDv _).trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact ((CoordinateExponential.christoffelBilinear B 0).le_opNorm₂ v w).trans
          (by gcongr)
      · apply ((CoordinateExponential.christoffelBilinear A 0).le_opNorm₂ _ _).trans
        exact mul_le_mul (mul_le_mul hGA (hDv v) (norm_nonneg _) (by positivity))
          (hDv w) (norm_nonneg _) (by positivity)
    _ ≤ (27 * C) * (ρ * N.epsilon + ρ ^ 2 * N'.epsilon) * ‖v‖ * ‖w‖ := by
      have he : 0 ≤ C * ρ * N.epsilon := by positivity
      nlinarith [mul_nonneg he (mul_nonneg (norm_nonneg v) (norm_nonneg w))]



theorem exists_intersecting_centeredEuclideanTransition_jet_bounds :
    ∃ K : ℝ, 0 < K ∧ ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N N' : EpsilonNeck g)
      (q q' : UnitTwoSphere) {s s' : ℝ},
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      s' ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
      N.coordinate_map (q, s) = N'.coordinate_map (q', s') →
      ‖fderiv ℝ (N.centeredEuclideanTransition N' q s q' s') 0‖ ≤ 6 ∧
      ‖fderiv ℝ (fderiv ℝ (N.centeredEuclideanTransition N' q s q' s')) 0‖ ≤
        K * (N.epsilon + N'.epsilon) := by
  obtain ⟨K, hK, hHess⟩ := exists_centeredEuclideanTransition_hessian_scaled_bound.{u}
  obtain ⟨epsilon0, hpos, hcap, hscale⟩ :=
    exists_intersecting_scale_control.{u} (α := 1) zero_lt_one
  refine ⟨4 * K, by positivity, epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' q q' s s' hN hN' hs hs' hx
  have hinter : (N'.carrier ∩ N.carrier).Nonempty := by
    refine ⟨N.coordinate_map (q, s), ?_, N.coordinate_map_mem ⟨mem_univ _, hs⟩⟩
    rw [hx]
    exact N'.coordinate_map_mem ⟨mem_univ _, hs'⟩
  have hratio := (abs_lt.mp (hscale N' N hN' hN hinter).2).2
  have hρ : 0 < N.scale / N'.scale := div_pos N.scale_pos N'.scale_pos
  have hρ2 : N.scale / N'.scale ≤ 2 := by linarith
  have hNpos := N.epsilon_pos
  have hN'pos := N'.epsilon_pos
  refine ⟨(N.norm_fderiv_centeredEuclideanTransition_le N' q q' hs hs' hx).trans
    (by linarith), (hHess N N' q q' hs hs' hx).trans ?_⟩
  have hsq : (N.scale / N'.scale) ^ 2 ≤ 4 := by nlinarith
  calc
    _ ≤ K * (2 * N.epsilon + 4 * N'.epsilon) := by
      gcongr
    _ ≤ (4 * K) * (N.epsilon + N'.epsilon) := by
      nlinarith [mul_nonneg hK.le N.epsilon_pos.le]

end PoincareConjecture.EpsilonNeck
