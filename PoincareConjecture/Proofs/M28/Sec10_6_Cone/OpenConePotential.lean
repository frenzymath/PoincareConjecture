import PoincareConjecture.Proofs.M28.Mathlib.RadiusSquareLipschitz
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicLocalPaths
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ChartSegment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalDilation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalQuadratic













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem locally_lipschitz_chart_of_riemannian_edist_bound
    (g : RiemannianMetric n M) (f : M → ℝ) {L : ℝ≥0}
    (hf : ∀ x y, EDist.edist (f x) (f y) ≤ (L : ℝ≥0∞) * g.edist x y) :
    ∀ p : M, ∃ V ∈ 𝓝 (extChartAt (𝓡 n) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 n) p).symm) V := by
  intro p
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let c := extChartAt (𝓡 n) p
  obtain ⟨C, _, hC⟩ :=
    eventually_enorm_mfderivWithin_symm_extChartAt_lt (𝓡 n) p
  have hC' : ∀ᶠ z in 𝓝 (c p), ‖mfderiv (𝓡 n) (𝓡 n) c.symm z‖ₑ < C := by
    simpa only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ,
      mfderivWithin_univ] using hC
  have ht : c.target ∈ 𝓝 (c p) :=
    (isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target p)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hC')
  refine ⟨Metric.ball (c p) r, Metric.ball_mem_nhds _ hr, L * C, ?_⟩
  intro x hx y hy
  have hsmooth (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball (c p) r) :
      ContMDiffAt (𝓡 n) (𝓡 n) 1 c.symm z := by
    simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ] using
      contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := 1) p (hball hz).1
  have hbound (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Metric.ball (c p) r) :
      ‖mfderiv (𝓡 n) (𝓡 n) c.symm z‖ₑ ≤ (C : ℝ≥0∞) :=
    (hball hz).2.le
  have hd := Poincare.riemannianEDist_le_mul_edist_of_convex
    (convex_ball (c p) r) hsmooth hbound hx hy
  change g.edist (c.symm x) (c.symm y) ≤ (C : ℝ≥0∞) * EDist.edist x y at hd
  calc
    EDist.edist (f (c.symm x)) (f (c.symm y)) ≤
        (L : ℝ≥0∞) * g.edist (c.symm x) (c.symm y) := hf _ _
    _ ≤ (L : ℝ≥0∞) * ((C : ℝ≥0∞) * EDist.edist x y) := mul_le_mul' le_rfl hd
    _ = ((L * C : ℝ≥0) : ℝ≥0∞) * EDist.edist x y := by
      rw [ENNReal.coe_mul, mul_assoc]

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.M28.ConePotential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem speed_eq_endpoint_distance
    {g : RiemannianMetric n M} {γ : ℝ → M} {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hγ : g.IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)))
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) :
    g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) =
      (g.edist (γ 0) (γ 1)).toReal := by
  have h0 : (0 : ℝ) ∈ Ioo (-epsilon) (1 + epsilon) := by
    constructor <;> linarith
  have hv := (hγ.hasDerivAt_chart_at h0 (γ 0) (mem_extChartAt_source _)).1
  have hh := hγ.initial_tangentNorm_eq_of_edist_segment hepsilon rfl hv hmin
  have hspeed := hγ.tangentNorm_initial h0 rfl hv
  have hh' := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0)
    (deriv (fun u => extChartAt (𝓡 n) (γ 0) (γ u)) 0) from Real.sqrt_nonneg _)] at hh'
  simp only [RiemannianMetric.chartCoefficients_self] at hspeed
  exact hspeed.trans hh'

omit [T2Space M] in
private theorem speed_affine {g : RiemannianMetric n M} {γ : ℝ → M}
    {a b : ℝ} (ha : 0 ≤ a)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) 1 γ b) :
    g.tangentNorm (γ (a * 0 + b))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t => γ (a * t + b)) 0 1) =
      a * g.tangentNorm (γ b) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ b 1) := by
  have hp : HasDerivAt (fun t : ℝ => a * t + b) a 0 := by
    simpa only [mul_one, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const b
  have hγ' : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (a * 0 + b) := by
    simpa only [mul_zero, zero_add] using hγ.mdifferentiableAt one_ne_zero
  have hd := congrArg (fun A => A (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n) 0
      hγ' hp.differentiableAt.mdifferentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t => γ (a * t + b)) 0 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (a * 0 + b)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => a * t + b) 0 1) at hd
  have hp' : fderiv ℝ (fun t : ℝ => a * t + b) 0 1 = a := by
    rw [fderiv_eq_smul_deriv, one_smul, hp.deriv]
  erw [mfderiv_eq_fderiv, hp'] at hd
  have hvel := hd.trans (by simpa only [smul_eq_mul, mul_one] using
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ (a * 0 + b)).map_smul a (1 : ℝ))
  rw [hvel]
  simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  exact congrArg (fun t : ℝ =>
    a * g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
    (by ring : a * 0 + b = b)

private theorem quadratic_of_local_distance_and_radial_law
    {X : Type*} [MetricSpace X] (g : RiemannianMetric n M)
    (j : M → X) (phi : X → ℝ)
    (hlocal : ∀ p : M, ∃ N : Set M, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ N, ∀ y ∈ N, edist (j x) (j y) = g.edist x y)
    (hvariation : ∀ x z y : M, ∀ᶠ a : ℝ in 𝓝 1, ∃ w : X,
      dist (j x) w ^ 2 = 2 * a ^ 2 * phi (j z) + 2 * phi (j x) -
        a * (2 * phi (j z) + 2 * phi (j x) - dist (j x) (j z) ^ 2) ∧
      dist (j y) w ^ 2 = 2 * a ^ 2 * phi (j z) + 2 * phi (j y) -
        a * (2 * phi (j z) + 2 * phi (j y) - dist (j y) (j z) ^ 2)) :
    ∀ (γ : ℝ → M) (epsilon : ℝ), 0 < epsilon →
      g.IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        phi (j (γ t)) = (1 - t) * phi (j (γ 0)) + t * phi (j (γ 1)) -
          t * (1 - t) * g.tangentNorm (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) ^ 2 / 2 := by
  intro γ epsilon hepsilon hγ
  let J := Ioo (-epsilon) (1 + epsilon)
  have hI : Icc (0 : ℝ) 1 ⊆ J := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  rw [hC 0 (hI (by simp))]
  apply Poincare.AncientVolume.ScalarRatio.interpolation_of_locally_quadratic
    isOpen_Ioo (convex_Ioo _ _).isPreconnected hI
  intro t₀ ht₀
  obtain ⟨N, hN, hpN, hmetric⟩ := hlocal (γ t₀)
  let J₀ := J ∩ γ ⁻¹' N
  have hJ₀ : IsOpen J₀ :=
    hγ.contMDiffOn.continuousOn.isOpen_inter_preimage isOpen_Ioo hN
  have ht₀' : t₀ ∈ J₀ := ⟨ht₀, hpN⟩
  have hγ₀ : g.IsGeodesicOn γ J₀ := fun t ht => hγ t ht.1
  obtain ⟨δ, hδ, hsub, hη, hηmin⟩ :=
    hγ₀.exists_minimizing_affine_neighborhood hJ₀ ht₀'
  let a := 2 * δ
  let b := t₀ - δ
  let η := fun t => γ (a * t + b)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : b ∈ J := (hsub ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩).1
  have hηN (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : η t ∈ N := by
    have ht' : a * t + b ∈ Ioo (t₀ - 3 * δ) (t₀ + 3 * δ) := by
      dsimp [a, b]
      constructor <;> nlinarith [ht.1, ht.2]
    exact (hsub ht').2
  have hspeed : g.tangentNorm (η 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 0 1) = a * C :=
    (speed_affine ha.le (hγ.contMDiffAt hb)).trans (congrArg (a * ·) (hC b hb))
  have hη' : g.IsGeodesicOn η (Ioo (-1 : ℝ) (1 + 1)) := by
    simpa only [one_add_one_eq_two] using hη
  have hdistance : dist (j (η 0)) (j (η 1)) = a * C := by
    rw [dist_edist, hmetric (η 0) (hηN 0 (by simp)) (η 1) (hηN 1 (by simp))]
    exact (speed_eq_endpoint_distance (by norm_num) hη' hηmin).symm.trans hspeed
  have hpairs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (j (η s)) (j (η t)) = |s - t| * dist (j (η 0)) (j (η 1)) := by
    have he := (hmetric (η s) (hηN s hs) (η t) (hηN t ht)).trans (hηmin s hs t ht)
    rw [← hmetric (η 0) (hηN 0 (by simp)) (η 1) (hηN 1 (by simp))] at he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg (s - t)),
      ← dist_edist] using congrArg ENNReal.toReal he
  have hformula (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      phi (j (η t)) = (1 - t) * phi (j (η 0)) + t * phi (j (η 1)) -
        t * (1 - t) * (a * C) ^ 2 / 2 := by
    have h := Poincare.AncientVolume.ScalarRatio.potential_interpolation_of_local_radial_variation
      phi (j (η 0)) (j (η t)) (j (η 1)) ht
      (by simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hpairs 0 (by simp) t ht)
      (by simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using
        hpairs t ht 1 (by simp))
      (fun _ _ => hvariation (η 0) (η t) (η 1))
    simpa only [hdistance] using h
  let A := phi (j (η 0))
  let D := phi (j (η 1))
  refine ⟨A - b * (D - A) / a + b * (a + b) * (C : ℝ) ^ 2 / 2,
    (D - A) / a - (a + 2 * b) * (C : ℝ) ^ 2 / 2, ?_⟩
  filter_upwards [Ioo_mem_nhds (by linarith : t₀ - δ < t₀)
    (by linarith : t₀ < t₀ + δ)] with t ht
  have hu : (t - b) / a ∈ Icc (0 : ℝ) 1 := by
    constructor
    · apply div_nonneg _ ha.le
      dsimp [b]
      linarith [ht.1]
    · apply (div_le_one ha).mpr
      dsimp [a, b]
      linarith [ht.2]
  have harg : a * ((t - b) / a) + b = t := by field_simp; ring
  have hh := hformula ((t - b) / a) hu
  change phi (j (γ (a * ((t - b) / a) + b))) =
    (1 - (t - b) / a) * A + (t - b) / a * D -
      (t - b) / a * (1 - (t - b) / a) * (a * C) ^ 2 / 2 at hh
  rw [harg] at hh
  rw [hh]
  field_simp
  ring

end PoincareConjecture.M28.ConePotential

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {X : Type*} [MetricSpace X]






theorem open_potential_of_ambient_isometry_and_local_radial_law
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (j : U → X) (hj : ∀ x y : U, edist (j x) (j y) = g.edist (x : M) (y : M))
    (phi : X → ℝ) {B : ℝ≥0} (hphi : LipschitzWith B phi)
    (hvariation : ∀ x z y : U, ∀ᶠ a : ℝ in 𝓝 1, ∃ w : X,
      dist (j x) w ^ 2 = 2 * a ^ 2 * phi (j z) + 2 * phi (j x) -
        a * (2 * phi (j z) + 2 * phi (j x) - dist (j x) (j z) ^ 2) ∧
      dist (j y) w ^ 2 = 2 * a ^ 2 * phi (j z) + 2 * phi (j y) -
        a * (2 * phi (j z) + 2 * phi (j y) - dist (j y) (j z) ^ 2)) :
    let f : U → ℝ := phi ∘ j
    (∀ p : U, ∃ V ∈ 𝓝 (extChartAt (𝓡 3) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 3) p).symm) V) ∧
    (∀ (γ : ℝ → U) (epsilon : ℝ), 0 < epsilon →
      (intrinsicOpenMetric g U).IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (intrinsicOpenMetric g U).tangentNorm (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ^ 2 / 2) ∧
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f := by
  let h := intrinsicOpenMetric g U
  let f : U → ℝ := phi ∘ j
  have hfbound (x y : U) : edist (f x) (f y) ≤ (B : ℝ≥0∞) * h.edist x y := by
    have hdist : edist (j x) (j y) ≤ h.edist x y := by
      rw [hj, intrinsicOpenMetric_edist]
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      apply le_sInf
      rintro L ⟨gamma, hsmooth, hstart, hend, _, rfl⟩
      exact Manifold.riemannianEDist_le_pathELength hsmooth hstart hend zero_le_one
    exact (hphi (j x) (j y)).trans (mul_le_mul' le_rfl hdist)
  have hLip := h.locally_lipschitz_chart_of_riemannian_edist_bound f hfbound
  have hlocal : ∀ p : U, ∃ N : Set U, IsOpen N ∧ p ∈ N ∧
      ∀ x ∈ N, ∀ y ∈ N, edist (j x) (j y) = h.edist x y := by
    intro p
    obtain ⟨W, hW, hpW, _, hEq⟩ := exists_open_intrinsic_distance_eq g U.isOpen p.property
    refine ⟨(Subtype.val : U → M) ⁻¹' W, hW.preimage continuous_subtype_val, hpW, ?_⟩
    intro x hx y hy
    rw [hj, intrinsicOpenMetric_edist]
    exact (hEq (x : M) hx (y : M) hy).symm
  have hquad := ConePotential.quadratic_of_local_distance_and_radial_law
    h j phi hlocal hvariation
  exact ⟨hLip, hquad, h.contMDiff_of_locally_lipschitz_geodesic_quadratic f hLip hquad⟩






theorem open_radius_potential_of_retained_isometry
    (g : RiemannianMetric 3 M) (K : Set M) (U : TopologicalSpace.Opens M)
    (hUK : (U : Set M) ⊆ K) (jK : K → X)
    (hjK : ∀ x y : K, edist (jK x) (jK y) = g.edist (x : M) (y : M))
    (r : X → ℝ) (hr : LipschitzWith 1 r) {B : ℝ≥0}
    (hB : ∀ x, |r x| ≤ (B : ℝ))
    (hvariation :
      let j : U → X := fun x => jK ⟨x, hUK x.property⟩
      ∀ x z y : U, ∀ᶠ a : ℝ in 𝓝 1, ∃ w : X,
        dist (j x) w ^ 2 = a ^ 2 * r (j z) ^ 2 + r (j x) ^ 2 -
          a * (r (j z) ^ 2 + r (j x) ^ 2 - dist (j x) (j z) ^ 2) ∧
        dist (j y) w ^ 2 = a ^ 2 * r (j z) ^ 2 + r (j y) ^ 2 -
          a * (r (j z) ^ 2 + r (j y) ^ 2 - dist (j y) (j z) ^ 2)) :
    let j : U → X := fun x => jK ⟨x, hUK x.property⟩
    let f : U → ℝ := fun x => r (j x) ^ 2 / 2
    (∀ p : U, ∃ V ∈ 𝓝 (extChartAt (𝓡 3) p p), ∃ C : ℝ≥0,
      LipschitzOnWith C (f ∘ (extChartAt (𝓡 3) p).symm) V) ∧
    (∀ (γ : ℝ → U) (epsilon : ℝ), 0 < epsilon →
      (intrinsicOpenMetric g U).IsGeodesicOn γ (Ioo (-epsilon) (1 + epsilon)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (intrinsicOpenMetric g U).tangentNorm (γ 0)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) ^ 2 / 2) ∧
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f := by
  let j : U → X := fun x => jK ⟨x, hUK x.property⟩
  apply open_potential_of_ambient_isometry_and_local_radial_law g U j
    (fun x y => hjK ⟨x, hUK x.property⟩ ⟨y, hUK y.property⟩)
    (fun x => r x ^ 2 / 2) (hr.half_sq_of_abs_le hB)
  intro x z y
  filter_upwards [hvariation x z y] with a ha
  obtain ⟨w, hx, hy⟩ := ha
  refine ⟨w, ?_, ?_⟩
  · rw [hx]
    ring
  · rw [hy]
    ring

end PoincareConjecture.M28
