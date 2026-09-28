import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.UnitInterval









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory PoincareConjecture
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Poincare.Geometry.Riemannian.SpaceForm

variable {n : ℕ}

private theorem norm_unitSphere (x : UnitSphere n) :
    ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

private theorem angle_eq_arccos_chord (x y : UnitSphere n) :
    InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y =
      Real.arccos (1 - dist x y ^ 2 / 2) := by
  rw [InnerProductGeometry.angle, norm_unitSphere, norm_unitSphere]
  simp only [one_mul, div_one]
  congr 1
  have hsq : dist x y ^ 2 = 2 - 2 * inner ℝ
      (x : EuclideanSpace ℝ (Fin (n + 1))) y := by
    simp only [Subtype.dist_eq, dist_eq_norm, norm_sub_sq_real, norm_unitSphere]
    ring
  linarith

private theorem roundSphere_pathELength_eq
    (γ : ℝ → UnitSphere n) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (a b : ℝ) :
    (roundSphereMetric n).pathELength γ a b =
      ∫⁻ t in Icc a b, ‖deriv (fun s => (γ s : EuclideanSpace ℝ (Fin (n + 1)))) t‖ₑ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  unfold RiemannianMetric.pathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  have hchain := mfderiv_comp t
    (contMDiff_coe_sphere.mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiable one_ne_zero t)
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (fun s => (γ s : EuclideanSpace ℝ (Fin (n + 1)))) t 1 =
      deriv (fun s => (γ s : EuclideanSpace ℝ (Fin (n + 1)))) t := by
    rw [mfderiv_eq_fderiv]
    rfl
  rw [← hd]
  rw [show (fun s => (γ s : EuclideanSpace ℝ (Fin (n + 1)))) =
    (((↑) : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) ∘ γ) from rfl]
  rw [hchain]
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  apply NNReal.eq
  simp only [coe_nnnorm, ContinuousLinearMap.comp_apply]
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  rfl

private theorem roundSphere_edist_le_pathELength
    (γ : ℝ → UnitSphere n) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    {a b : ℝ} (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ (roundSphereMetric n).pathELength γ a b := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  have hη : ContDiff ℝ 1 (fun s => (γ s : EuclideanSpace ℝ (Fin (n + 1)))) :=
    contMDiff_iff_contDiff.mp (contMDiff_coe_sphere.comp hγ)
  rw [roundSphere_pathELength_eq γ hγ]
  simpa only [Subtype.edist_eq, edist_comm (γ a : EuclideanSpace ℝ (Fin (n + 1))),
    edist_eq_enorm_sub] using
    enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hη.contDiffOn hab

private theorem sphereAngle_eq_twice_arcsin (x y : UnitSphere n) :
    InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y =
      2 * Real.arcsin (dist x y / 2) := by
  have htwo : dist x y ≤ 2 := by
    calc
      dist x y ≤ ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ + ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
        dist_le_norm_add_norm (x : EuclideanSpace ℝ (Fin (n + 1))) y
      _ = 2 := by rw [norm_unitSphere, norm_unitSphere]; norm_num
  have hlow : -(1 : ℝ) ≤ dist x y / 2 := by linarith [dist_nonneg (x := x) (y := y)]
  have hhigh : dist x y / 2 ≤ 1 := by linarith
  have hcos : Real.cos (2 * Real.arcsin (dist x y / 2)) = 1 - dist x y ^ 2 / 2 := by
    rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (Real.arcsin (dist x y / 2)),
      Real.sin_arcsin hlow hhigh]
    ring
  rw [angle_eq_arccos_chord, ← hcos]
  apply Real.arccos_cos
  · exact mul_nonneg (by norm_num) (Real.arcsin_nonneg.mpr (div_nonneg dist_nonneg (by norm_num)))
  · linarith [Real.arcsin_le_pi_div_two (dist x y / 2)]

private theorem exists_sphereAngle_le_mul_dist {c : ℝ} (hc : 1 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : UnitSphere n, dist x y < δ →
      InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y ≤ c * dist x y := by
  let f := fun s : ℝ => 2 * Real.arcsin (s / 2)
  have hd : HasDerivAt f 1 0 := by
    have h0 : HasDerivAt Real.arcsin 1 (id (0 : ℝ) / 2) := by
      simpa using Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)
    have hh := (h0.comp 0 ((hasDerivAt_id (0 : ℝ)).div_const 2)).const_mul 2
    simpa [f] using hh
  have hlim : Tendsto (fun s : ℝ => f s / s) (𝓝[>] 0) (𝓝 1) := by
    simpa [f, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, f s / s < c := hlim.eventually (gt_mem_nhds hc)
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hsmall
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  by_cases heq : x = y
  · subst y
    simp [angle_eq_arccos_chord]
  have hpos : 0 < dist x y := dist_pos.mpr heq
  have hh := hsub ⟨hpos, hxy⟩
  rw [sphereAngle_eq_twice_arcsin]
  exact ((div_lt_iff₀ hpos).mp hh).le

private theorem ennreal_le_of_real_factors {a b : ℝ≥0∞}
    (h : ∀ c : ℝ, 1 < c → a ≤ ENNReal.ofReal c * b) : a ≤ b := by
  by_cases hb : b = ⊤
  · simp [hb]
  have hfinite : ENNReal.ofReal (2 : ℝ) * b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hfinite (h 2 (by norm_num))
  apply (ENNReal.toReal_le_toReal ha hb).mp
  apply (le_iff_forall_one_lt_le_mul₀ ENNReal.toReal_nonneg).mpr
  intro c hc
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb) (h c hc)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ c)] at hh
  simpa only [mul_comm] using hh

private theorem sphereAngle_le_pathELength
    (γ : ℝ → UnitSphere n) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) :
    ENNReal.ofReal (InnerProductGeometry.angle
      (γ 0 : EuclideanSpace ℝ (Fin (n + 1))) (γ 1)) ≤
      (roundSphereMetric n).pathELength γ 0 1 := by
  let g := roundSphereMetric n
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) := ⟨g.toRiemannianMetric⟩
  let angle (x y : UnitSphere n) := InnerProductGeometry.angle
    (x : EuclideanSpace ℝ (Fin (n + 1))) y
  have hnonneg (x y : UnitSphere n) : 0 ≤ angle x y := InnerProductGeometry.angle_nonneg _ _
  apply ennreal_le_of_real_factors
  intro c hc
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨δ, hδ, hangle⟩ := exists_sphereAngle_le_mul_dist (n := n) hc
  let U := fun s : unitInterval => (fun t : unitInterval => γ t) ⁻¹' Metric.ball (γ s) (δ / 2)
  have hUopen : ∀ s, IsOpen (U s) := fun s =>
    Metric.isOpen_ball.preimage (hγ.continuous.comp continuous_subtype_val)
  have hUcover : univ ⊆ ⋃ s, U s := by
    intro s _
    apply mem_iUnion.mpr
    exact ⟨s, by change dist (γ s) (γ s) < δ / 2; rw [dist_self]; positivity⟩
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hUopen hUcover
  have hstep (k : ℕ) : ENNReal.ofReal (angle (γ (t k)) (γ (t (k + 1)))) ≤
      ENNReal.ofReal c * g.pathELength γ (t k) (t (k + 1)) := by
    obtain ⟨s, hts⟩ := hsub k
    have htime : (t k : ℝ) ≤ t (k + 1) := htmono (Nat.le_succ k)
    have hleft : dist (γ (t k)) (γ s) < δ / 2 := hts ⟨le_rfl, htime⟩
    have hright : dist (γ (t (k + 1))) (γ s) < δ / 2 := hts ⟨htime, le_rfl⟩
    have hshort : dist (γ (t k)) (γ (t (k + 1))) < δ := by
      have hh := dist_triangle (γ (t k)) (γ s) (γ (t (k + 1)))
      rw [dist_comm (γ s) (γ (t (k + 1)))] at hh
      linarith
    have hchord := roundSphere_edist_le_pathELength γ hγ htime
    calc
      _ ≤ ENNReal.ofReal (c * dist (γ (t k)) (γ (t (k + 1)))) :=
        ENNReal.ofReal_le_ofReal (hangle _ _ hshort)
      _ = ENNReal.ofReal c * edist (γ (t k)) (γ (t (k + 1))) := by
        rw [ENNReal.ofReal_mul hc0, edist_dist]
      _ ≤ _ := by gcongr
  have hind (k : ℕ) : ENNReal.ofReal (angle (γ 0) (γ (t k))) ≤
      ENNReal.ofReal c * g.pathELength γ 0 (t k) := by
    induction k with
    | zero =>
        rw [ht0]
        have hzero : angle (γ 0) (γ 0) = 0 := by simp [angle, angle_eq_arccos_chord]
        change ENNReal.ofReal (angle (γ 0) (γ 0)) ≤ _
        rw [hzero, ENNReal.ofReal_zero]
        exact bot_le
    | succ k ih =>
        calc
          _ ≤ ENNReal.ofReal (angle (γ 0) (γ (t k)) + angle (γ (t k)) (γ (t (k + 1)))) :=
            ENNReal.ofReal_le_ofReal (InnerProductGeometry.angle_le_angle_add_angle _ _ _)
          _ = ENNReal.ofReal (angle (γ 0) (γ (t k))) +
              ENNReal.ofReal (angle (γ (t k)) (γ (t (k + 1)))) :=
            ENNReal.ofReal_add (hnonneg _ _) (hnonneg _ _)
          _ ≤ ENNReal.ofReal c * g.pathELength γ 0 (t k) +
              ENNReal.ofReal c * g.pathELength γ (t k) (t (k + 1)) := add_le_add ih (hstep k)
          _ = _ := by
            rw [← mul_add]
            congr 1
            exact Manifold.pathELength_add (I := 𝓡 n) (γ := γ)
              (t k).property.1 (htmono (Nat.le_succ k))
  have hfinal := hind N
  rw [hN N le_rfl] at hfinal
  exact hfinal

private theorem norm_orthogonal_combination_sq
    (x v : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ = 1) (hv : ‖v‖ = 1)
    (hxv : inner ℝ x v = 0) (a b : ℝ) : ‖a • x + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, hxv, hx, hv]
  simp [Real.norm_eq_abs, sq_abs]

private theorem roundSphere_edist_le_of_arc
    (x y : UnitSphere n) (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hv : ‖v‖ = 1) (hxv : inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) v = 0)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hy : (y : EuclideanSpace ℝ (Fin (n + 1))) =
      Real.cos θ • (x : EuclideanSpace ℝ (Fin (n + 1))) + Real.sin θ • v) :
    (roundSphereMetric n).edist x y ≤ ENNReal.ofReal θ := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let η : ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun t => Real.cos t • (x : EuclideanSpace ℝ (Fin (n + 1))) + Real.sin t • v
  have hnorm (t : ℝ) : ‖η t‖ = 1 := by
    have hh := norm_orthogonal_combination_sq (x : EuclideanSpace ℝ (Fin (n + 1))) v
      (norm_unitSphere x) hv hxv (Real.cos t) (Real.sin t)
    dsimp only [η]
    nlinarith [Real.sin_sq_add_cos_sq t, norm_nonneg (η t)]
  have hmem (t : ℝ) : η t ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hnorm t
  let γ : ℝ → UnitSphere n := Set.codRestrict η _ hmem
  have hη : ContDiff ℝ 1 η := by dsimp only [η]; fun_prop
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ := hη.contMDiff.codRestrict_sphere hmem
  have hγ0 : γ 0 = x := by apply Subtype.ext; simp [γ, η]
  have hγθ : γ θ = y := by apply Subtype.ext; exact hy.symm
  have hd (t : ℝ) : deriv η t =
      (-Real.sin t) • (x : EuclideanSpace ℝ (Fin (n + 1))) + Real.cos t • v :=
    (((Real.hasDerivAt_cos t).smul_const (x : EuclideanSpace ℝ (Fin (n + 1)))).add
      ((Real.hasDerivAt_sin t).smul_const v)).deriv
  have hspeed (t : ℝ) : ‖deriv η t‖ₑ = 1 := by
    have hh := norm_orthogonal_combination_sq (x : EuclideanSpace ℝ (Fin (n + 1))) v
      (norm_unitSphere x) hv hxv (-Real.sin t) (Real.cos t)
    rw [← hd] at hh
    have hn : ‖deriv η t‖ = 1 := by nlinarith [Real.sin_sq_add_cos_sq t, norm_nonneg (deriv η t)]
    rw [enorm_eq_nnnorm]
    have hnn : ‖deriv η t‖₊ = 1 := NNReal.eq hn
    simp [hnn]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  have hle : (roundSphereMetric n).edist x y ≤
      (roundSphereMetric n).pathELength γ 0 θ :=
    Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 hγθ hθ
  apply hle.trans_eq
  rw [roundSphere_pathELength_eq γ hγ]
  change (∫⁻ t in Icc (0 : ℝ) θ, ‖deriv η t‖ₑ) = ENNReal.ofReal θ
  simp [hspeed]

private theorem exists_unit_orthogonal (hn : 1 ≤ n) (x : UnitSphere n) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)), ‖v‖ = 1 ∧
      inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) v = 0 := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let B := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere x)
  let i : Fin n := ⟨0, by omega⟩
  exact ⟨B i, B.orthonormal.norm_eq_one i,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (B i).property⟩

private theorem roundSphere_metric_edist_le_angle (hn : 1 ≤ n) (x y : UnitSphere n) :
    (roundSphereMetric n).edist x y ≤ ENNReal.ofReal
      (InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y) := by
  by_cases heq : x = y
  · subst y
    simp [angle_eq_arccos_chord, RiemannianMetric.edist, Manifold.riemannianEDist_self]
  have hxne : (x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := ne_zero_of_mem_unit_sphere x
  by_cases hanti : (y : EuclideanSpace ℝ (Fin (n + 1))) = -x
  · obtain ⟨v, hv, hxv⟩ := exists_unit_orthogonal hn x
    have hangle : InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y = Real.pi := by
      rw [hanti, InnerProductGeometry.angle_neg_right]
      simp [InnerProductGeometry.angle_self hxne]
    rw [hangle]
    apply roundSphere_edist_le_of_arc x y v hv hxv Real.pi_pos.le
    simpa using hanti
  let θ := InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin (n + 1))) y
  have hθ0 : 0 < θ := by
    apply lt_of_le_of_ne (InnerProductGeometry.angle_nonneg _ _)
    intro hzero
    apply heq
    apply Subtype.ext
    exact InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq hzero.symm
      ((norm_unitSphere x).trans (norm_unitSphere y).symm)
  have hθpi : θ < Real.pi := by
    apply lt_of_le_of_ne (InnerProductGeometry.angle_le_pi _ _)
    intro hpi
    have hinner : inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) y = -1 := by
      simpa only [norm_unitSphere, mul_one] using
        InnerProductGeometry.inner_eq_neg_mul_norm_of_angle_eq_pi hpi
    have hneg := (inner_eq_neg_one_iff_of_norm_eq_one (norm_unitSphere x) (norm_unitSphere y)).mp hinner
    apply hanti
    simpa only [neg_neg] using (congrArg Neg.neg hneg).symm
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hcos : inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) y = Real.cos θ :=
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one (norm_unitSphere x) (norm_unitSphere y)
  have hcos' : inner ℝ (y : EuclideanSpace ℝ (Fin (n + 1))) x = Real.cos θ := by
    rw [real_inner_comm]
    exact hcos
  let w : EuclideanSpace ℝ (Fin (n + 1)) := y - Real.cos θ • (x : EuclideanSpace ℝ (Fin (n + 1)))
  have hwnorm : ‖w‖ = Real.sin θ := by
    have hsq : ‖w‖ ^ 2 = 1 - Real.cos θ ^ 2 := by
      dsimp only [w]
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hcos',
        norm_unitSphere, norm_unitSphere]
      simp only [Real.norm_eq_abs, mul_one, sq_abs, one_pow]
      ring
    nlinarith [Real.sin_sq_add_cos_sq θ, norm_nonneg w]
  have hwinner : inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) w = 0 := by
    dsimp only [w]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_unitSphere, hcos]
    ring
  let v := (Real.sin θ)⁻¹ • w
  have hv : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), hwnorm,
      inv_mul_cancel₀ hs.ne']
  have hxv : inner ℝ (x : EuclideanSpace ℝ (Fin (n + 1))) v = 0 := by
    dsimp only [v]
    rw [real_inner_smul_right, hwinner, mul_zero]
  apply roundSphere_edist_le_of_arc x y v hv hxv hθ0.le
  dsimp only [v]
  rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  dsimp only [w]
  module

private theorem sphereAngle_le_metric_edist (x y : UnitSphere n) :
    ENNReal.ofReal (InnerProductGeometry.angle
      (x : EuclideanSpace ℝ (Fin (n + 1))) y) ≤ (roundSphereMetric n).edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : UnitSphere n → Type _) :=
    ⟨(roundSphereMetric n).toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := 𝓡 n) hr zero_lt_one
  have hle := sphereAngle_le_pathELength γ hγ
  rw [h0, h1] at hle
  exact hle.trans_lt hlen



theorem roundSphereMetric_edist_eq_angle
    {n : ℕ} (hn : 1 ≤ n) (x y : UnitSphere n) :
    (roundSphereMetric n).edist x y =
      ENNReal.ofReal (Real.arccos (1 - dist x y ^ 2 / 2)) := by
  rw [← angle_eq_arccos_chord]
  exact le_antisymm (roundSphere_metric_edist_le_angle hn x y) (sphereAngle_le_metric_edist x y)

end Poincare.Geometry.Riemannian.SpaceForm
