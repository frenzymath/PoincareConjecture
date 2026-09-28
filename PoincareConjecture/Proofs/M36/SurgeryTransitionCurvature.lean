import PoincareConjecture.Proofs.M36.SurgeryTransitionGeometry
import PoincareConjecture.Proofs.M36.ConformalAbsorption










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M36

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

section Scaling

variable {X : Type u} [TopologicalSpace X] [ChartedSpace E₃ X]
  [IsManifold (𝓡 3) ∞ X] {g : RiemannianMetric 3 X}

theorem scalarCurvature_positiveScaling_const (D : LeviCivitaData g)
    {c : ℝ} (hc : 0 < c)
    (D' : LeviCivitaData (positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc)))
    (x : X) : D'.scalarCurvature x = c⁻¹ * D.scalarCurvature x := by
  let F : X → ℝ := fun _ => -Real.log c / 2
  have hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F := contMDiff_const
  have hmetric : positiveScaling g (fun _ => c) contMDiff_const (fun _ => hc) =
      positiveScaling g (fun y => Real.exp (-2 * F y))
        (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _) := by
    have he : (fun y => Real.exp (-2 * F y)) = fun _ => c := by
      funext y
      change Real.exp (-2 * (-Real.log c / 2)) = c
      rw [show -2 * (-Real.log c / 2) = Real.log c by ring, Real.exp_log hc]
    congr 1
    exact he.symm
  revert D'
  rw [hmetric]
  intro D'
  have he : Real.exp (2 * (-Real.log c / 2)) = c⁻¹ := by
    rw [show 2 * (-Real.log c / 2) = -Real.log c by ring, Real.exp_neg, Real.exp_log hc]
  have h := scalarCurvature_positiveScaling_profile g D F hF D'
    (fun _ => 0) (fun _ => -Real.log c / 2) contDiff_const x contMDiffAt_const
    (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [deriv_const', deriv_const, he, zero_mul, mul_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero, sub_zero] using h

end Scaling

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

noncomputable def surgeryOutputConformalExponent (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q r : ℝ) :
    SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon) → ℝ :=
  standardCapConformalExponent g₀ C q N.epsilon r ∘
    surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon)

theorem surgeryOutputConformalExponent_contMDiff (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q : ℝ) {r : ℝ} (hr : 0 < r) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (surgeryOutputConformalExponent g₀ N C q r) :=
  (standardCapConformalExponent_contDiff g₀ C q N.epsilon hr).contMDiff.comp
    (surgeryBallInclusion_contMDiff g₀ _)

theorem surgeryOutputConformalExponent_germ (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (C q : ℝ) {r : ℝ} (hr : 0 < r)
    (hrA : r ≤ g₀.cylindrical_end.radius)
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryOutputHeight g₀ N y < 2) :
    surgeryOutputConformalExponent g₀ N C q r =ᶠ[𝓝 y]
      fun z => smoothProfile C q N.epsilon (surgeryOutputHeight g₀ N z) := by
  filter_upwards [(isOpen_lt (surgeryOutputHeight_continuous g₀ N)
    continuous_const).mem_nhds hy] with z hz
  exact standardCapConformalExponent_eq_on_transition g₀ C q N.epsilon hr hrA hz.le

theorem surgeryMetric_normalized_eq_conformal (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (C q eta r : ℝ) (hlambda : 0 < N.connection.scalarCurvature N.center)
    (heta : 0 < eta) (hr : 0 < r) :
    positiveScaling (surgeryMetric g₀ N hcut C q eta r hlambda heta hr)
      (fun _ => N.connection.scalarCurvature N.center) contMDiff_const (fun _ => hlambda) =
    positiveScaling (surgeryPreconformalMetric g₀ N hcut eta heta)
      (fun y => Real.exp (-2 * surgeryOutputConformalExponent g₀ N C q r y))
      (contMDiff_exp_neg_two (surgeryOutputConformalExponent_contMDiff g₀ N C q hr))
      (fun _ => Real.exp_pos _) := by
  have hinner :
      (positiveScaling (surgeryMetric g₀ N hcut C q eta r hlambda heta hr)
        (fun _ => N.connection.scalarCurvature N.center) contMDiff_const
        (fun _ => hlambda)).inner =
      (positiveScaling (surgeryPreconformalMetric g₀ N hcut eta heta)
        (fun y => Real.exp (-2 * surgeryOutputConformalExponent g₀ N C q r y))
        (contMDiff_exp_neg_two (surgeryOutputConformalExponent_contMDiff g₀ N C q hr))
        (fun _ => Real.exp_pos _)).inner := by
    funext y
    ext v w
    change N.connection.scalarCurvature N.center *
      (surgeryMetric g₀ N hcut C q eta r hlambda heta hr).inner y v w =
      Real.exp (-2 * surgeryOutputConformalExponent g₀ N C q r y) *
        (surgeryPreconformalMetric g₀ N hcut eta heta).inner y v w
    rw [surgeryMetric_preconformal_inner]
    rw [surgeryOutputConformalExponent, Function.comp_apply,
      standardCapConformalExponent_exp]
    rfl
  generalize hleft : positiveScaling (surgeryMetric g₀ N hcut C q eta r hlambda heta hr)
    (fun _ => N.connection.scalarCurvature N.center) contMDiff_const
    (fun _ => hlambda) = A at hinner ⊢
  generalize hright : positiveScaling (surgeryPreconformalMetric g₀ N hcut eta heta)
    (fun y => Real.exp (-2 * surgeryOutputConformalExponent g₀ N C q r y))
    (contMDiff_exp_neg_two (surgeryOutputConformalExponent_contMDiff g₀ N C q hr))
    (fun _ => Real.exp_pos _) = B at hinner ⊢
  cases A
  cases B
  cases hinner
  rfl

theorem exists_surgeryTransition_curvature (q : ℝ) (hq : 8 ≤ q) :
    ∃ C0 : ℝ, 100 * q < C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∃ delta : ℝ, 0 < delta ∧
      ∀ (g₀ : StandardInitialMetric)
        {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
        ∀ (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹), N.epsilon ≤ delta →
        ∀ (r : ℝ) (hlambda : 0 < N.connection.scalarCurvature N.center)
          (heta : 0 < 1 - 6 * N.epsilon) (hr : 0 < r), r ≤ g₀.cylindrical_end.radius →
        ∀ (D : LeviCivitaData
            (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr))
          (DJ : LeviCivitaData (surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta))
          (y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)),
          0 < surgeryOutputHeight g₀ N y → surgeryOutputHeight g₀ N y < 2 →
          N.connection.scalarCurvature N.center / 2 ≤ D.scalarCurvature y ∧
          N.connection.scalarCurvature N.center * DJ.scalarCurvature y ≤ D.scalarCurvature y ∧
          D.negativeCurvaturePart y ≤
            N.connection.scalarCurvature N.center * DJ.negativeCurvaturePart y ∧
          ((∀ a b : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair
                (surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta) y a b →
              0 < DJ.sectionalCurvature y a b) →
            ∀ a b : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair
                (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr) y a b →
              0 < D.sectionalCurvature y a b) ∧
          (1 ≤ surgeryOutputHeight g₀ N y → ∀ a b : TangentSpace (𝓡 3) y,
            LeviCivitaData.IsOrthonormalPair
              (surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr) y a b →
            0 < D.sectionalCurvature y a b) := by
  obtain ⟨deltaG, hdG, K, hK, hgeometry⟩ := exists_surgeryPreconformalGeometry
  obtain ⟨C0, hC0, habs⟩ := exists_conformalAbsorption K q hK hq
  refine ⟨C0, hC0, ?_⟩
  intro C hC
  obtain ⟨deltaA, hdA, habs⟩ := habs C hC
  refine ⟨min deltaG deltaA, lt_min hdG hdA, ?_⟩
  intro g₀ M _ _ _ g N hcut hsmall r hlambda heta hr hrA D DJ y hy0 hy2
  let lambda := N.connection.scalarCurvature N.center
  let H := surgeryMetric g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr
  let J := surgeryPreconformalMetric g₀ N hcut (1 - 6 * N.epsilon) heta
  let F := surgeryOutputConformalExponent g₀ N C q r
  have hF := surgeryOutputConformalExponent_contMDiff g₀ N C q hr
  let HN := positiveScaling H (fun _ => lambda) contMDiff_const (fun _ => hlambda)
  let HC := positiveScaling J (fun z => Real.exp (-2 * F z))
    (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)
  have hmetric : HN = HC :=
    surgeryMetric_normalized_eq_conformal g₀ N hcut C q (1 - 6 * N.epsilon) r hlambda heta hr
  have hgeom := hgeometry g₀ N hcut (hsmall.trans (min_le_left _ _)) heta DJ y hy0.le hy2
  obtain ⟨DN⟩ := exists_leviCivitaData HN
  have hnormal : DJ.scalarCurvature y ≤ DN.scalarCurvature y ∧
      DN.negativeCurvaturePart y ≤ DJ.negativeCurvaturePart y ∧
      ((∀ a b : TangentSpace (𝓡 3) y, LeviCivitaData.IsOrthonormalPair J y a b →
          0 < DJ.sectionalCurvature y a b) →
        ∀ a b : TangentSpace (𝓡 3) y, LeviCivitaData.IsOrthonormalPair HN y a b →
          0 < DN.sectionalCurvature y a b) ∧
      (1 ≤ surgeryOutputHeight g₀ N y → ∀ a b : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair HN y a b → 0 < DN.sectionalCurvature y a b) := by
    revert DN
    rw [hmetric]
    intro DN
    apply habs J DJ F hF DN (surgeryOutputHeight g₀ N) y N.epsilon N.epsilon_pos
      (hsmall.trans (min_le_right _ _)) hy0 hy2.le
      (surgeryOutputHeight_contMDiffAt g₀ N hy2)
      (surgeryOutputConformalExponent_germ g₀ N C q hr hrA hy2) hgeom.gradient
    · intro a ha
      have hn : (surgeryPreconformalMetric g₀ N hcut
          (1 - 6 * N.epsilon) heta).tangentNorm y a = 1 := by
        rw [RiemannianMetric.tangentNorm, ha, Real.sqrt_one]
      simpa only [hn, mul_one] using hgeom.hessian a a
    · exact hgeom.laplacian
    · exact hgeom.scalar
    · exact hgeom.sectional
    · exact hgeom.axial
  have hscaleR := scalarCurvature_positiveScaling_const D hlambda DN y
  have hscaleN := negativeCurvaturePart_positiveScaling_const D hlambda DN y
  have hR : lambda * DJ.scalarCurvature y ≤ D.scalarCurvature y := by
    have h := mul_le_mul_of_nonneg_left hnormal.1 hlambda.le
    rw [hscaleR] at h
    simpa only [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] using h
  have hNeg : D.negativeCurvaturePart y ≤ lambda * DJ.negativeCurvaturePart y := by
    have h := mul_le_mul_of_nonneg_left hnormal.2.1 hlambda.le
    rw [hscaleN] at h
    simpa only [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] using h
  have hposTransport
      (hpositive : ∀ a b : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair HN y a b → 0 < DN.sectionalCurvature y a b)
      (a b : TangentSpace (𝓡 3) y) (hab : LeviCivitaData.IsOrthonormalPair H y a b) :
      0 < D.sectionalCurvature y a b := by
    have hsqrt : Real.sqrt lambda ≠ 0 := (Real.sqrt_pos.mpr hlambda).ne'
    have hpair : LeviCivitaData.IsOrthonormalPair HN y
        ((Real.sqrt lambda)⁻¹ • a) ((Real.sqrt lambda)⁻¹ • b) := by
      rw [positiveScaling_const_orthonormal_iff H hlambda]
      change LeviCivitaData.IsOrthonormalPair H y
        (Real.sqrt lambda • ((Real.sqrt lambda)⁻¹ • a))
        (Real.sqrt lambda • ((Real.sqrt lambda)⁻¹ • b))
      simpa only [smul_smul, mul_inv_cancel₀ hsqrt, one_smul] using hab
    have hp := hpositive _ _ hpair
    rw [sectionalCurvature_smul_pair DN y a b (inv_ne_zero hsqrt) (inv_ne_zero hsqrt),
      sectionalCurvature_positiveScaling_const_of_orthonormal D hlambda DN y hab] at hp
    have h := mul_pos hlambda hp
    simpa only [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] using h
  refine ⟨?_, hR, hNeg, ?_, ?_⟩
  · have h := (mul_le_mul_of_nonneg_left hgeom.scalar hlambda.le).trans hR
    simpa only [div_eq_mul_inv, one_mul] using h
  · intro hpositive
    exact hposTransport (hnormal.2.2.1 hpositive)
  · intro hy1
    exact hposTransport (hnormal.2.2.2 hy1)





theorem surgeryPreconformalMetric_collar_curvature (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹)
    (eta : ℝ) (heta : 0 < eta)
    (DJ : LeviCivitaData (surgeryPreconformalMetric g₀ N hcut eta heta))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryOutputHeight g₀ N y < 5 / 4) :
    DJ.scalarCurvature y = (N.connection.scalarCurvature N.center)⁻¹ *
        N.connection.scalarCurvature (surgeryRetainedInverse g₀ N y) ∧
    DJ.negativeCurvaturePart y = (N.connection.scalarCurvature N.center)⁻¹ *
        N.connection.negativeCurvaturePart (surgeryRetainedInverse g₀ N y) ∧
    ((∀ a b : TangentSpace (𝓡 3) (surgeryRetainedInverse g₀ N y),
        LeviCivitaData.IsOrthonormalPair g (surgeryRetainedInverse g₀ N y) a b →
        0 < N.connection.sectionalCurvature (surgeryRetainedInverse g₀ N y) a b) →
      ∀ a b : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair
          (surgeryPreconformalMetric g₀ N hcut eta heta) y a b →
        0 < DJ.sectionalCurvature y a b) := by
  let J := surgeryPreconformalMetric g₀ N hcut eta heta
  let T := surgeryRetainedInverse g₀ N
  let U : Set (SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)) :=
    {z | surgeryOutputHeight g₀ N z < 5 / 4}
  have hU : IsOpen U := isOpen_lt (surgeryOutputHeight_continuous g₀ N) continuous_const
  have hne : ∀ z ∈ U, surgeryBallInclusion g₀ (surgeryOuterRadius g₀ N.epsilon) z ≠ 0 := by
    intro z hz hzero
    change standardSurgeryHeight g₀ (surgeryBallInclusion g₀ _ z) < 5 / 4 at hz
    rw [hzero, standardSurgeryHeight_zero] at hz
    linarith [g₀.cylindrical_end.radius_pos]
  have hT : ContMDiffOn (𝓡 3) (𝓡 3) ∞ T U := fun z hz =>
    (surgeryRetainedInverse_contMDiffAt g₀ N hcut (hne z hz)).contMDiffWithinAt
  have hmetric : ∀ z ∈ U, ∀ a b : TangentSpace (𝓡 3) z,
      J.inner z a b = (normalizedNeckMetric N).inner (T z)
        (mfderiv (𝓡 3) (𝓡 3) T z a) (mfderiv (𝓡 3) (𝓡 3) T z b) := by
    intro z hz a b
    have hweight : surgeryNeckWeight g₀ N z = 1 := neckCutoff_eq_one (le_of_lt hz)
    change (surgeryPreconformalMetric g₀ N hcut eta heta).inner z a b = _
    rw [surgeryPreconformalMetric_inner, hweight]
    simp only [sub_self, zero_mul, add_zero, one_mul]
    rfl
  let DN := normalizedNeckConnection N
  have hR := scalarCurvature_eq_of_local_isometry DJ DN hU hT hmetric hy
  have hN := negativeCurvaturePart_eq_of_local_isometry DJ DN hU hT hmetric hy
  refine ⟨hR.trans (scalarCurvature_positiveScaling_const N.connection N.scalar_center_pos DN _),
    hN.trans (negativeCurvaturePart_positiveScaling_const N.connection N.scalar_center_pos DN _),
    ?_⟩
  intro hpositive a b hab
  have hpair : LeviCivitaData.IsOrthonormalPair (normalizedNeckMetric N) (T y)
      (mfderiv (𝓡 3) (𝓡 3) T y a) (mfderiv (𝓡 3) (𝓡 3) T y b) := by
    unfold LeviCivitaData.IsOrthonormalPair at hab ⊢
    rw [← hmetric y hy a a, ← hmetric y hy b b, ← hmetric y hy a b]
    exact hab
  let lambda := N.connection.scalarCurvature N.center
  have hlambda : 0 < lambda := N.scalar_center_pos
  have hpair' := (positiveScaling_const_orthonormal_iff g hlambda (T y)
    (mfderiv (𝓡 3) (𝓡 3) T y a) (mfderiv (𝓡 3) (𝓡 3) T y b)).mp hpair
  have hsec := sectionalCurvature_positiveScaling_const_of_orthonormal N.connection
    hlambda DN (T y) hpair'
  rw [sectionalCurvature_smul_pair DN (T y)
    (mfderiv (𝓡 3) (𝓡 3) T y a) (mfderiv (𝓡 3) (𝓡 3) T y b)
    (Real.sqrt_pos.mpr hlambda).ne' (Real.sqrt_pos.mpr hlambda).ne'] at hsec
  rw [sectionalCurvature_eq_of_local_isometry DJ DN hU hT hmetric hy, hsec]
  exact mul_pos (inv_pos.mpr hlambda) (hpositive _ _ hpair')





theorem surgeryMetric_scalar_retained (g₀ : StandardInitialMetric) (N : EpsilonNeck g)
    (hcut : surgeryCapRadius g₀ < N.epsilon⁻¹) (C q eta r : ℝ)
    (hlambda : 0 < N.connection.scalarCurvature N.center) (heta : 0 < eta) (hr : 0 < r)
    (hq : 0 < q) (hrA : r ≤ g₀.cylindrical_end.radius)
    (D : LeviCivitaData (surgeryMetric g₀ N hcut C q eta r hlambda heta hr))
    {y : SurgeryBall.{u} g₀ (surgeryOuterRadius g₀ N.epsilon)}
    (hy : surgeryOutputHeight g₀ N y ≤ 0) :
    D.scalarCurvature y = N.connection.scalarCurvature (surgeryRetainedInverse g₀ N y) := by
  let lambda := N.connection.scalarCurvature N.center
  let H := surgeryMetric g₀ N hcut C q eta r hlambda heta hr
  let J := surgeryPreconformalMetric g₀ N hcut eta heta
  let F := surgeryOutputConformalExponent g₀ N C q r
  have hF := surgeryOutputConformalExponent_contMDiff g₀ N C q hr
  let HN := positiveScaling H (fun _ => lambda) contMDiff_const (fun _ => hlambda)
  let HC := positiveScaling J (fun z => Real.exp (-2 * F z))
    (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)
  have hmetric : HN = HC :=
    surgeryMetric_normalized_eq_conformal g₀ N hcut C q eta r hlambda heta hr
  obtain ⟨DJ⟩ := exists_leviCivitaData J
  obtain ⟨DN⟩ := exists_leviCivitaData HN
  have hy2 : surgeryOutputHeight g₀ N y < 2 := by linarith only [hy]
  have hz : smoothProfile C q N.epsilon (surgeryOutputHeight g₀ N y) = 0 :=
    smoothProfile_eq_zero hq hy
  have hd : deriv (smoothProfile C q N.epsilon) (surgeryOutputHeight g₀ N y) = 0 := by
    rw [smoothProfile_deriv hq, hz, mul_zero]
  have hdd : deriv (deriv (smoothProfile C q N.epsilon))
      (surgeryOutputHeight g₀ N y) = 0 := by
    rw [smoothProfile_second_deriv hq, hz, mul_zero]
  have hnormal : DN.scalarCurvature y = DJ.scalarCurvature y := by
    revert DN
    rw [hmetric]
    intro DN
    rw [scalarCurvature_positiveScaling_profile J DJ F hF DN (surgeryOutputHeight g₀ N)
      (smoothProfile C q N.epsilon) (smoothProfile_contDiff C q N.epsilon) y
      (surgeryOutputHeight_contMDiffAt g₀ N hy2)
      (surgeryOutputConformalExponent_germ g₀ N C q hr hrA hy2)]
    simp only [hz, hd, hdd, mul_zero, Real.exp_zero, zero_mul, add_zero,
      zero_pow (by norm_num : 2 ≠ 0), sub_zero, one_mul]
  have hscale := scalarCurvature_positiveScaling_const D hlambda DN y
  have hcollar := (surgeryPreconformalMetric_collar_curvature g₀ N hcut eta heta DJ
    (by linarith only [hy] : surgeryOutputHeight g₀ N y < 5 / 4)).1
  calc
    D.scalarCurvature y = lambda * DN.scalarCurvature y := by
      rw [hscale]
      change _ = lambda * (lambda⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]
    _ = lambda * DJ.scalarCurvature y := congrArg (lambda * ·) hnormal
    _ = N.connection.scalarCurvature (surgeryRetainedInverse g₀ N y) := by
      rw [hcollar]
      change lambda * (lambda⁻¹ * _) = _
      rw [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul]

end PoincareConjecture.M36
