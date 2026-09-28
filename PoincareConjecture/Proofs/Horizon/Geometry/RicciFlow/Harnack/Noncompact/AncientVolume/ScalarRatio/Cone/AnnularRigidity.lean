import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalQuadratic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RadialGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Universe
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology NNReal ENNReal Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ}

private theorem subtype_chart_coefficients
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (g : RiemannianMetric n U) (h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hmetric : ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      g.inner x v w = h.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    (p : U) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm y = h.euclideanCoefficients y := by
  let c := extChartAt (𝓡 n) p
  have hinv : mfderiv (𝓡 n) (𝓡 n) c.symm y =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hh := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hh
    change (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n))
      (c.symm y)).comp (mfderiv (𝓡 n) (𝓡 n) c.symm y) = _ at hh
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hh
    ext v
    exact congrArg (fun A => A v) hh
  ext v w
  change g.inner (c.symm y)
    (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y w) = h.inner y v w
  rw [hinv]
  change g.inner (c.symm y) v w = h.inner y v w
  rw [hmetric]
  exact congrArg (fun z => h.inner z v w) (c.right_inv hy)

theorem IsGeodesicOn.subtype_val_of_inner_eq
    {U : Opens (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n U} {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (hmetric : ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      g.inner x v w = h.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    {γ : ℝ → U} {J : Set ℝ} (hγ : g.IsGeodesicOn γ J) (hJ : IsOpen J) :
    h.IsGeodesicOn (fun t => (γ t : EuclideanSpace ℝ (Fin n))) J := by
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun t => γ t
  have hdata (t : ℝ) (ht : t ∈ J) :
      HasDerivAt q (deriv q t) t ∧ HasDerivAt (deriv q)
        (-coordinateChristoffel h.euclideanCoefficients (q t) (deriv q t) (deriv q t)) t := by
    let c := extChartAt (𝓡 n) (γ t)
    have ho := hγ.hasDerivAt_chart_at ht (γ t) (mem_extChartAt_source _)
    change HasDerivAt q (deriv q t) t ∧ HasDerivAt (deriv q)
      (-coordinateChristoffel (g.pullbackCoefficients c.symm) (q t) (deriv q t) (deriv q t)) t at ho
    have hcoeff : g.pullbackCoefficients c.symm =ᶠ[𝓝 (q t)] h.euclideanCoefficients := by
      filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) (γ t)).mem_nhds
        (mem_extChartAt_target (γ t))] with y hy
      exact subtype_chart_coefficients U g h hmetric (γ t) hy
    have hΓ : coordinateChristoffel (g.pullbackCoefficients c.symm) (q t) =
        coordinateChristoffel h.euclideanCoefficients (q t) := by
      unfold coordinateChristoffel
      rw [hcoeff.self_of_nhds, hcoeff.fderiv_eq]
    rw [hΓ] at ho
    exact ho
  have hcoeff : h.pullbackCoefficients id = h.euclideanCoefficients := by
    ext x v w
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  have hh := h.isGeodesicOn_chart_curve (0 : EuclideanSpace ℝ (Fin n)) hJ
    (q := q) (w := deriv q) (fun t ht => by
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
        PartialEquiv.refl_coe, PartialEquiv.refl_target, mem_univ, hcoeff, true_and]
        using hdata t ht)
  simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq] using hh

theorem tangentNorm_subtype_curve_of_inner_eq
    {U : Opens (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n U} {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (hmetric : ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      g.inner x v w = h.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    {γ : ℝ → U} {t : ℝ} (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ t) :
    g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) =
      h.tangentNorm (γ t : EuclideanSpace ℝ (Fin n))
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => (γ s : EuclideanSpace ℝ (Fin n))) t 1) := by
  have hval : MDifferentiableAt (𝓡 n) (𝓡 n)
      (Subtype.val : U → EuclideanSpace ℝ (Fin n)) (γ t) :=
    (contMDiff_subtype_val (I := 𝓡 n) (n := ∞)).mdifferentiable (by simp) (γ t)
  have hv := congrArg (fun A => A (1 : ℝ)) (mfderiv_comp t hval hγ)
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hv
  change mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => (γ s : EuclideanSpace ℝ (Fin n))) t 1 =
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1 at hv
  unfold tangentNorm
  rw [hv, hmetric]

private theorem minimizing_speed_eq_distance
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {ε : ℝ}
    (hε : 0 < ε) (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) :
    g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) =
      (g.edist (γ 0) (γ 1)).toReal := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hv := (hγ.hasDerivAt_chart_at h0 (γ 0) (mem_extChartAt_source _)).1
  have hh := hγ.initial_tangentNorm_eq_of_edist_segment hε rfl hv hmin
  have hspeed := hγ.tangentNorm_initial h0 rfl hv
  have hh' := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0)
    (deriv (fun u => extChartAt (𝓡 n) (γ 0) (γ u)) 0) from Real.sqrt_nonneg _)] at hh'
  simp only [chartCoefficients_self] at hspeed
  exact hspeed.trans hh'

private theorem euclidean_speed_affine
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ} (ha : 0 ≤ a)
    (hγ : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ b) :
    g.tangentNorm (γ (a * 0 + b))
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t => γ (a * t + b)) 0 1) =
      a * g.tangentNorm (γ b) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ b 1) := by
  have hp : HasDerivAt (fun t : ℝ => a * t + b) a 0 := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id (0 : ℝ)).const_mul a).add_const b
  have hγ' : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b) := by
    simpa only [mul_zero, zero_add] using hγ.mdifferentiableAt one_ne_zero
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n) 0
      hγ' hp.differentiableAt.mdifferentiableAt)
  change mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun t => γ (a * t + b)) 0 1 =
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun t => a * t + b) 0 1) at hd
  have hp' : fderiv ℝ (fun t : ℝ => a * t + b) 0 1 = a := by
    rw [fderiv_eq_smul_deriv, one_smul, hp.deriv]
  have hp'' : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun t : ℝ => a * t + b) 0 1 = a := by
    rw [mfderiv_eq_fderiv]
    exact hp'
  rw [hp''] at hd
  have hvel := hd.trans (by simpa only [smul_eq_mul, mul_one] using
    (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ (a * 0 + b)).map_smul a (1 : ℝ))
  rw [hvel]
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  exact congrArg (fun t : ℝ =>
    a * g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1))
    (by ring : a * 0 + b = b)

theorem geodesic_quadratic_on_of_minimizing_segments
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (V : Set (EuclideanSpace ℝ (Fin n)))
    (hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) V →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {ε : ℝ} (hε : 0 < ε)
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγV : MapsTo γ (Ioo (-ε) (1 + ε)) V) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        g.tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2 := by
  let J := Ioo (-ε) (1 + ε)
  have hI : Icc (0 : ℝ) 1 ⊆ J := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by linarith)
  rw [hC 0 (hI (by simp))]
  apply Poincare.AncientVolume.ScalarRatio.interpolation_of_locally_quadratic
    isOpen_Ioo (convex_Ioo _ _).isPreconnected hI
  intro t₀ ht₀
  obtain ⟨δ, hδ, hsub, hη, hηmin⟩ :=
    hγ.exists_minimizing_affine_neighborhood isOpen_Ioo ht₀
  let a := 2 * δ
  let b := t₀ - δ
  let η := fun t => γ (a * t + b)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : b ∈ J := hsub ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have hspeed : g.tangentNorm (η 0)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η 0 1) = a * C :=
    (euclidean_speed_affine ha.le (hγ.contMDiffAt hb)).trans (congrArg (a * ·) (hC b hb))
  have hη' : g.IsGeodesicOn η (Ioo (-1 : ℝ) (1 + 1)) := by
    simpa only [one_add_one_eq_two] using hη
  have hηV : MapsTo η (Icc (0 : ℝ) 1) V := by
    intro t ht
    apply hγV
    apply hsub
    dsimp [a, b]
    constructor <;> nlinarith [ht.1, ht.2]
  have hdist : (g.edist (η 0) (η 1)).toReal = a * C :=
    (minimizing_speed_eq_distance (by norm_num) hη' hηmin).symm.trans hspeed
  have hformula := hquad η 1 (by norm_num) hη' hηV hηmin
  rw [hdist] at hformula
  let A := f (η 0)
  let D := f (η 1)
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
  change f (γ (a * ((t - b) / a) + b)) =
    (1 - (t - b) / a) * A + (t - b) / a * D -
      (t - b) / a * (1 - (t - b) / a) * (a * C) ^ 2 / 2 at hh
  rw [harg] at hh
  rw [hh]
  field_simp
  ring

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio

theorem locally_lipschitz_opens_of_lipschitzOn_closedBall
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    {ρ : ℝ} (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 ρ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : ℝ≥0}
    (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ)) :
    ∀ p : U, ∃ V ∈ 𝓝 (extChartAt (𝓡 n) p p), ∃ D : ℝ≥0,
      LipschitzOnWith D
        ((fun x : U => f x) ∘ (extChartAt (𝓡 n) p).symm) V := by
  intro p
  let c := extChartAt (𝓡 n) p
  have hsub : c.target ⊆ Metric.closedBall 0 ρ := by
    intro y hy
    have hval : (c.symm y : EuclideanSpace ℝ (Fin n)) = y := c.right_inv hy
    rw [← hval]
    exact Metric.ball_subset_closedBall (hU (c.symm y).property)
  refine ⟨c.target, (isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds
    (mem_extChartAt_target p), C, ?_⟩
  intro x hx y hy
  change edist (f (c.symm x : EuclideanSpace ℝ (Fin n)))
    (f (c.symm y : EuclideanSpace ℝ (Fin n))) ≤ C * edist x y
  rw [show (c.symm x : EuclideanSpace ℝ (Fin n)) = x from c.right_inv hx,
    show (c.symm y : EuclideanSpace ℝ (Fin n)) = y from c.right_inv hy]
  exact hLip (hsub hx) (hsub hy)

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RicciFlow

private theorem isLocalDiffeomorph_coordinate_inclusion
    {n : ℕ} {V U : Opens (EuclideanSpace ℝ (Fin n))} (hVU : V ≤ U) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (Opens.inclusion hVU : V → U) := by
  intro x
  let : Nonempty V := ⟨x⟩
  have he : Topology.IsOpenEmbedding (Opens.inclusion hVU : V → U) :=
    Topology.IsOpenEmbedding.inclusion hVU (V.isOpen.preimage continuous_subtype_val)
  let e := he.toOpenPartialHomeomorph
  let d : PartialDiffeomorph (𝓡 n) (𝓡 n) V U ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := (contMDiff_inclusion (I := 𝓡 n) hVU).contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff V e.symm e.target y).mp
        apply (contMDiff_subtype_val (I := 𝓡 n) (n := ∞) y).contMDiffWithinAt.congr
        · intro z hz
          exact congrArg Subtype.val (e.right_inv hz)
        · exact congrArg Subtype.val (e.right_inv hy) }
  exact ⟨d, mem_univ x, fun _ _ => rfl⟩

private theorem mfderiv_coordinate_inclusion
    {n : ℕ} {V U : Opens (EuclideanSpace ℝ (Fin n))} (hVU : V ≤ U) (x : V) :
    mfderiv (𝓡 n) (𝓡 n) (Opens.inclusion hVU : V → U) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hval : MDifferentiable (𝓡 n) (𝓡 n)
      (Subtype.val : U → EuclideanSpace ℝ (Fin n)) :=
    (contMDiff_subtype_val (I := 𝓡 n) (n := ∞)).mdifferentiable (by simp)
  have hinc := (contMDiff_inclusion (I := 𝓡 n) (n := ∞) hVU).mdifferentiable (by simp)
  have hh := mfderiv_comp x (hval (Opens.inclusion hVU x)) (hinc x)
  change mfderiv (𝓡 n) (𝓡 n) (Subtype.val : V → EuclideanSpace ℝ (Fin n)) x =
    (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → EuclideanSpace ℝ (Fin n))
      (Opens.inclusion hVU x)).comp
      (mfderiv (𝓡 n) (𝓡 n) (Opens.inclusion hVU : V → U) x) at hh
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal,
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hh
  ext v
  exact (congrArg (fun A => A v) hh).symm

theorem curvatureTensorNorm_eq_zero_of_annular_minimizing_identity
    {n : ℕ} (hC : RicciFlowCurvatureTheory.{u})
    {U : Opens (EuclideanSpace ℝ (Fin n))} (F : RicciFlow n U (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (hmetric : ∀ (x : U) (v w : EuclideanSpace ℝ (Fin n)),
      (F.metric 0).inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {ρ : ℝ}
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 ρ)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ))
    (hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) U →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2) :
    ∀ x, (F.connection 0).curvatureTensorNorm x = 0 := by
  have hquadF : ∀ (γ : ℝ → U) (ε : ℝ), 0 < ε →
      (F.metric 0).IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → ∀ t ∈ Icc (0 : ℝ) 1,
      f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
        (F.metric 0).tangentNorm (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1) ^ 2 / 2 := by
    intro γ ε hε hγ t ht
    have hγE := hγ.subtype_val_of_inner_eq hmetric isOpen_Ioo
    have hh := g.geodesic_quadratic_on_of_minimizing_segments f U hquad hε hγE
      (fun s _ => (γ s).property) t ht
    have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have hs := RiemannianMetric.tangentNorm_subtype_curve_of_inner_eq hmetric
      ((hγ.contMDiffAt h0).mdifferentiableAt one_ne_zero)
    rw [← hs] at hh
    exact hh
  have hLipF :=
    Poincare.AncientVolume.ScalarRatio.locally_lipschitz_opens_of_lipschitzOn_closedBall U hU f hLip
  have hf := (F.metric 0).contMDiff_of_locally_lipschitz_geodesic_quadratic
    (fun x : U => f x) hLipF hquadF
  obtain ⟨hsmooth, hgrad⟩ :=
    (F.connection 0).gradient_homothetic_of_geodesic_quadratic hf hquadF
  apply curvatureTensorNorm_eq_zero_of_terminal_homothetic_field_small hC F hoperator
    ((F.connection 0).gradient (fun x : U => f x)) hsmooth (c := 1) (by norm_num)
  intro x v
  simpa only [one_smul] using hgrad x v

theorem curvatureTensorNorm_eq_zero_on_of_annular_minimizing_identity
    {n : ℕ} (hC : RicciFlowCurvatureTheory.{u})
    {U : Opens (EuclideanSpace ℝ (Fin n))} (F : RicciFlow n U (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U)
    (hmetric : ∀ (x : U), (x : EuclideanSpace ℝ (Fin n)) ∈ V →
      ∀ v w : EuclideanSpace ℝ (Fin n),
        (F.metric 0).inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {ρ : ℝ}
    (hV : (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 ρ)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ))
    (hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) V →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2) :
    ∀ x : U, (x : EuclideanSpace ℝ (Fin n)) ∈ V →
      (F.connection 0).curvatureTensorNorm x = 0 := by
  let e : V → U := Opens.inclusion hVU
  have he : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e :=
    isLocalDiffeomorph_coordinate_inclusion hVU
  let G := F.pullbackWithConnection e he (fun t =>
    ((F.metric t).pullbackOfLocalDiffeomorph e he).leviCivitaData)
  have hGinner (t : ℝ) (x : V) (v w : EuclideanSpace ℝ (Fin n)) :
      (G.metric t).inner x v w = (F.metric t).inner (e x) v w := by
    change (F.metric t).inner (e x)
      (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) = _
    rw [mfderiv_coordinate_inclusion hVU x]
    rfl
  have hGoperator : ∀ t ≤ 0, ∀ x, (G.connection t).NonnegativeCurvatureOperator x := by
    intro t ht x
    exact ((G.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      (F.connection t) isOpen_univ he.contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x)).2 (hoperator t ht (e x))
  have hGmetric (x : V) (v w : EuclideanSpace ℝ (Fin n)) :
      (G.metric 0).inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w :=
    (hGinner 0 x v w).trans (hmetric (e x) x.property v w)
  have hflat := G.curvatureTensorNorm_eq_zero_of_annular_minimizing_identity hC
    hGoperator g hGmetric f hV hLip hquad
  intro x hx
  let y : V := ⟨x, hx⟩
  have hnat := (G.connection 0).curvatureTensorNorm_eq_of_local_isometry
    (F.connection 0) isOpen_univ he.contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ y)
  have hpoint : e y = x := Subtype.ext rfl
  rw [hpoint] at hnat
  exact hnat.symm.trans (hflat y)

theorem false_of_scalar_one_annular_minimizing_identity
    {n : ℕ} (hC : RicciFlowCurvatureTheory.{u})
    {U : Opens (EuclideanSpace ℝ (Fin n))} (F : RicciFlow n U (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U)
    (hmetric : ∀ (x : U), (x : EuclideanSpace ℝ (Fin n)) ∈ V →
      ∀ v w : EuclideanSpace ℝ (Fin n),
        (F.metric 0).inner x v w = g.inner (x : EuclideanSpace ℝ (Fin n)) v w)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {ρ : ℝ}
    (hV : (V : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 ρ)
    {C : ℝ≥0} (hLip : LipschitzOnWith C f (Metric.closedBall 0 ρ))
    (hquad : ∀ (γ : ℝ → EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0 < ε →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) → MapsTo γ (Icc (0 : ℝ) 1) V →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1)) →
      ∀ t ∈ Icc (0 : ℝ) 1,
        f (γ t) = (1 - t) * f (γ 0) + t * f (γ 1) - t * (1 - t) *
          (g.edist (γ 0) (γ 1)).toReal ^ 2 / 2)
    (x : U) (hx : (x : EuclideanSpace ℝ (Fin n)) ∈ V)
    (hscalar : (F.connection 0).scalarCurvature x = 1) : False := by
  have hflat := F.curvatureTensorNorm_eq_zero_on_of_annular_minimizing_identity
    hC hoperator g V hVU hmetric f hV hLip hquad x hx
  have hh := (F.connection 0).abs_scalarCurvature_le_curvatureTensorNorm x
  rw [hflat, hscalar] at hh
  norm_num at hh

end PoincareConjecture.RicciFlow
