import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthNative
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthBall
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance
import PoincareConjecture.Proofs.M13.Length

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M47

open Poincare.Geometry.Riemannian.SpaceForm

variable {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
  {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
  (N : StandardEvolvingNeck atlas G v gamma z
    (Icc (-v * (G.connection v).scalarCurvature z) 0))
  (hsmall : gamma ≤ 1 / 1200)
  (hdisjoint : Disjoint N.patch.carrier
    {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
  (hshort : v * (G.connection v).scalarCurvature z < 1 + gamma)

include hsmall hdisjoint hshort

theorem exists_standard_initial_neck_sphere_path
    (q r : UnitTwoSphere) {a : ℝ} (ha : a ∈ Ioo (-gamma⁻¹) gamma⁻¹) :
    ∃ p : ℝ → StandardCapSpace,
      p 0 = N.patch.coordinate (q, a) ∧ p 1 = N.patch.coordinate (r, a) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∃ s : UnitTwoSphere, p t = N.patch.coordinate (s, a)) ∧
      g0.metric.pathELength p 0 1 < ENNReal.ofReal ((51 / 50 : ℝ) * 6) := by
  let f : UnitTwoSphere → StandardCapSpace := fun s => N.patch.coordinate (s, a)
  have hfcoord (s : UnitTwoSphere) :
      ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.patch.coordinate (s, a) :=
    N.patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ha⟩)
  have hf : ContMDiff (𝓡 2) (𝓡 3) 1 f := by
    intro s
    exact ((hfcoord s).comp s
      (contMDiffAt_id.prodMk contMDiffAt_const)).of_le (by simp)
  have hd (s : UnitTwoSphere) (w : TangentSpace (𝓡 2) s) :
      mfderiv (𝓡 2) (𝓡 3) f s w =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.patch.coordinate (s, a) (w, 0) := by
    dsimp only [TangentSpace] at w ⊢
    change mfderiv (𝓡 2) (𝓡 3)
      (N.patch.coordinate ∘ fun s : UnitTwoSphere => (s, a)) s w = _
    have h := mfderiv_comp_apply s ((hfcoord s).mdifferentiableAt (by simp))
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const) w
    simp only [id_eq, mfderiv_prod_left] at h
    exact h
  let C : ℝ := (51 / 50 : ℝ) * Real.sqrt 2
  have hC : 0 < C := by dsimp only [C]; positivity
  have hspeed (s : UnitTwoSphere) (w : TangentSpace (𝓡 2) s) :
      g0.metric.tangentNorm (f s) (mfderiv (𝓡 2) (𝓡 3) f s w) ≤
        C * (roundSphereMetric 2).tangentNorm s w := by
    have hb := standard_initial_neck_birth_native_upper N hsmall hdisjoint hshort
      (s, a) ha (w, 0)
    have hi : g0.metric.inner (f s) (mfderiv (𝓡 2) (𝓡 3) f s w)
        (mfderiv (𝓡 2) (𝓡 3) f s w) ≤
        C ^ 2 * (roundSphereMetric 2).inner s w w := by
      rw [hd]
      dsimp only [C]
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      simpa only [roundCylinderPullback, EvolvingRoundCylinderMetric,
        roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner,
        sub_zero, mul_one, zero_mul, add_zero, mul_assoc, f] using hb
    change Real.sqrt _ ≤ C * Real.sqrt _
    exact (Real.sqrt_le_sqrt hi).trans_eq (by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le])
  have hdist : (roundSphereMetric 2).edist q r < ENNReal.ofReal (4 : ℝ) := by
    rw [roundSphereMetric_edist_eq_angle (by norm_num)]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr
    exact (Real.arccos_le_pi _).trans_lt Real.pi_lt_four
  obtain ⟨p, hp0, hp1, hp, hlength⟩ := M13.exists_pathELength_lt _ hdist
  refine ⟨f ∘ p, ?_, ?_, hf.comp_contMDiffOn hp, ?_, ?_⟩
  · simp only [Function.comp_apply, hp0, f]
  · simp only [Function.comp_apply, hp1, f]
  · intro t _
    exact ⟨p t, rfl⟩
  have hlen := (roundSphereMetric 2).pathELength_comp_le_of_pointwise_tangentNorm_le
    g0.metric f (U := univ) (fun s _ => hf s) hC.le
    (fun s _ w => hspeed s w) p 0 1 hp (fun _ _ => mem_univ _)
  apply hlen.trans_lt
  calc
    _ < ENNReal.ofReal C * ENNReal.ofReal (4 : ℝ) :=
      ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
        ENNReal.ofReal_ne_top hlength
    _ ≤ ENNReal.ofReal ((51 / 50 : ℝ) * 6) := by
      rw [← ENNReal.ofReal_mul hC.le]
      apply ENNReal.ofReal_le_ofReal
      have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      dsimp only [C]
      linarith

theorem standard_initial_neck_axis_path
    (q : UnitTwoSphere) {a b R : ℝ} (hR : R ≤ gamma⁻¹)
    (ha : a ∈ Ioo (-R) R) (hb : b ∈ Ioo (-R) R) :
    let p := fun t : ℝ => N.patch.coordinate (q, a + t * (b - a))
    p 0 = N.patch.coordinate (q, a) ∧ p 1 = N.patch.coordinate (q, b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1) ∧
      MapsTo p (Icc (0 : ℝ) 1) (N.patch.coordinate '' (univ ×ˢ Ioo (-R) R)) ∧
      g0.metric.pathELength p 0 1 ≤ ENNReal.ofReal ((51 / 50 : ℝ) * |b - a|) := by
  let c := fun t : ℝ => a + t * (b - a)
  let f := fun t : ℝ => (q, c t)
  have hc : ContDiff ℝ ∞ c := contDiff_const.add (contDiff_id.mul contDiff_const)
  have hf : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f :=
    contMDiff_const.prodMk hc.contMDiff
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : c t ∈ Ioo (-R) R := by
    have h := convex_Ioo (-R) R ha hb (sub_nonneg.mpr ht.2) ht.1
      (by ring : 1 - t + t = 1)
    convert! h using 1
    dsimp only [c, smul_eq_mul]
    ring
  have hfull (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      c t ∈ Ioo (-gamma⁻¹) gamma⁻¹ :=
    ⟨(neg_le_neg hR).trans_lt (hmem t ht).1, (hmem t ht).2.trans_le hR⟩
  have hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (N.patch.coordinate ∘ f) (Icc (0 : ℝ) 1) :=
    (N.patch.coordinate_smooth.comp hf.contMDiffOn
      (fun t ht => ⟨mem_univ _, hfull t ht⟩)).of_le (by simp)
  refine ⟨by simp, by simp, hp, ?_, ?_⟩
  · intro t ht
    exact ⟨f t, ⟨mem_univ _, hmem t ht⟩, rfl⟩
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g0.metric.tangentNorm (N.patch.coordinate (f t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (N.patch.coordinate ∘ f) t 1) ≤
        (51 / 50 : ℝ) * |b - a| := by
    have hcoord : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        N.patch.coordinate (q, c t) := (N.patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ q, hfull t ht⟩)).mdifferentiableAt
        (by simp)
    have hdt : mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) f t 1 = (0, b - a) := by
      have hd : HasDerivAt c (b - a) t := by
        convert! ((hasDerivAt_id t).mul_const (b - a)).const_add a using 1
        simp
      change mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (fun t : ℝ => (q, c t)) t 1 = _
      rw [mfderiv_prodMk mdifferentiableAt_const hd.differentiableAt.mdifferentiableAt,
        mfderiv_const, mfderiv_eq_fderiv]
      change (0, fderiv ℝ c t 1) = (0, b - a)
      rw [hd.hasFDerivAt.fderiv]
      simp
    rw [mfderiv_comp_apply t hcoord (hf.mdifferentiableAt (by simp)), hdt]
    have hi := standard_initial_neck_birth_native_upper N hsmall hdisjoint hshort
      (f t) (hfull t ht) (0, b - a)
    have hmodel : EvolvingRoundCylinderMetric 0 (f t) (0, b - a) (0, b - a) =
        (b - a) ^ 2 := by
      simp [EvolvingRoundCylinderMetric, pow_two]
    rw [hmodel] at hi
    have hi' : g0.metric.inner (N.patch.coordinate (f t))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.patch.coordinate (f t) (0, b - a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.patch.coordinate (f t) (0, b - a)) ≤
        ((51 / 50 : ℝ) * |b - a|) ^ 2 := by
      simpa only [roundCylinderPullback, mul_pow, sq_abs] using hi
    exact (Real.sqrt_le_sqrt hi').trans_eq (Real.sqrt_sq (by positivity))
  rw [g0.metric.pathELength_eq_lintegral_tangentNorm]
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal ((51 / 50 : ℝ) * |b - a|) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact ENNReal.ofReal_le_ofReal (hspeed t ht)
    _ = _ := by simp

theorem exists_standard_initial_neck_strip_paths
    {R : ℝ} (hR : R ≤ gamma⁻¹) (q r : UnitTwoSphere) {a b : ℝ}
    (ha : a ∈ Ioo (-R) R) (hb : b ∈ Ioo (-R) R) :
    ∃ p₁ p₂ : ℝ → StandardCapSpace,
      p₁ 0 = N.patch.coordinate (q, a) ∧
      p₁ 1 = N.patch.coordinate (r, a) ∧
      p₂ 0 = N.patch.coordinate (r, a) ∧
      p₂ 1 = N.patch.coordinate (r, b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p₁ (Icc 0 1) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p₂ (Icc 0 1) ∧
      MapsTo p₁ (Icc (0 : ℝ) 1) (N.patch.coordinate '' (univ ×ˢ Ioo (-R) R)) ∧
      MapsTo p₂ (Icc (0 : ℝ) 1) (N.patch.coordinate '' (univ ×ˢ Ioo (-R) R)) ∧
      g0.metric.pathELength p₁ 0 1 + g0.metric.pathELength p₂ 0 1 <
        ENNReal.ofReal ((51 / 50 : ℝ) * (6 + |b - a|)) := by
  have hafull : a ∈ Ioo (-gamma⁻¹) gamma⁻¹ :=
    ⟨(neg_le_neg hR).trans_lt ha.1, ha.2.trans_le hR⟩
  obtain ⟨p₁, hp10, hp11, hp₁, hmem₁, hlen₁⟩ :=
    exists_standard_initial_neck_sphere_path N hsmall hdisjoint hshort q r hafull
  let p₂ := fun t : ℝ => N.patch.coordinate (r, a + t * (b - a))
  obtain ⟨hp20, hp21, hp₂, hmem₂, hlen₂⟩ :=
    standard_initial_neck_axis_path N hsmall hdisjoint hshort r hR ha hb
  refine ⟨p₁, p₂, hp10, hp11, hp20, hp21, hp₁, hp₂, ?_, hmem₂, ?_⟩
  · intro t ht
    obtain ⟨s, hs⟩ := hmem₁ t ht
    exact ⟨(s, a), ⟨mem_univ _, ha⟩, hs.symm⟩
  calc
    _ < ENNReal.ofReal ((51 / 50 : ℝ) * 6) +
        ENNReal.ofReal ((51 / 50 : ℝ) * |b - a|) :=
      ENNReal.add_lt_add_of_lt_of_le
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlen₂) hlen₁ hlen₂
    _ = _ := by
      rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← mul_add]

end PoincareConjecture.M47
