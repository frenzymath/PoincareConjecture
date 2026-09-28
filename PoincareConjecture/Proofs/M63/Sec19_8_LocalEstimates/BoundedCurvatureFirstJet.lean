import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetDissipation
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetAmbientBounds
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple











set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63FirstJetSquared_bound_of_curvature_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hRiemann : ∀ s ∈ Icc a b, ∀ p : M, ∀ v : Fin 5 → TangentSpace (𝓡 n) p,
      (∀ i, (F.metric s).tangentNorm p (v i) ≤ 1) →
        |(F.connection s).covariantTensorDerivative
          (F.connection s).riemannEvaluation p v| ≤ K)
    (hSecond : ∀ s ∈ Icc a b, ∀ p : M, ∀ v : Fin 4 → TangentSpace (𝓡 n) p,
      (∀ i, (F.metric s).tangentNorm p (v i) ≤ 1) →
        |(F.connection s).covariantTensorDerivative
          ((F.connection s).covariantTensorDerivative
            (F.connection s).ricciEvaluation) p v| ≤ K)
    (hcurv : ∀ s ∈ Ioo a b, ∀ y, m62CurvatureSquared F c s y ≤ R) :
    let C := 14 * R + 10 * K + 1 + 4 * R ^ 3 + 2 * R * K * (7 * R + 6) +
      (K * (46 * R + 32)) ^ 2
    let lambda := 1 + C
    let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
    let D := C + lambda * D0
    ∀ x t, t ∈ Ioo a b → t - a ≤ 1 →
      m63CurvatureJetSquared F c 1 t x ≤ (lambda * R + D) / (t - a) := by
  let C := 14 * R + 10 * K + 1 + 4 * R ^ 3 + 2 * R * K * (7 * R + 6) +
    (K * (46 * R + 32)) ^ 2
  let lambda := 1 + C
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  let D := C + lambda * D0
  let q : ℝ → ℝ → ℝ := fun y s => m62CurvatureSquared F c s y
  let beta : ℝ → ℝ → ℝ := fun y s => m63CurvatureJetSquared F c 1 s y
  let chi : ℝ → ℝ → ℝ := fun y s => m63CurvatureJetSquared F c 2 s y
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlambda : 0 ≤ lambda := by dsimp only [lambda]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hq (y s : ℝ) : 0 ≤ q y s := curvatureSquared_nonneg F c s y
  have hbeta (y s : ℝ) : 0 ≤ beta y s :=
    ((F.metric s).toRiemannianMetric.toCore (c y s)).re_inner_nonneg _
  have hchi (y s : ℝ) : 0 ≤ chi y s :=
    ((F.metric s).toRiemannianMetric.toCore (c y s)).re_inner_nonneg _
  have hbetaPDE (y s : ℝ) (hs : s ∈ Ioo a b) :
      deriv (beta y) s - m62ArcSecondDerivative F c s (fun z => beta z s) y ≤
        -chi y s + C * beta y s + C :=
    m63FirstJetSquared_dissipation F c hc hK hR hBounds hs y (hcurv s hs y)
      (hRiemann s (Ioo_subset_Icc_self hs) (c y s))
      (hSecond s (Ioo_subset_Icc_self hs) (c y s))
  have hqPDE (y s : ℝ) (hs : s ∈ Ioo a b) :
      deriv (q y) s - m62ArcSecondDerivative F c s (fun z => q z s) y ≤
        -2 * beta y s + D0 := by
    have hraw := spatial_squared_bound F c hc hK hK hK hBounds hs y
    have hsplit := spatialDerivative_norm_split F c hc hs y
    change beta y s = (F.metric s).inner (c y s)
      (m62SpatialNormalDerivative F c s y) (m62SpatialNormalDerivative F c s y) +
      q y s ^ 2 at hsplit
    have hqR : q y s ≤ R := hcurv s hs y
    have hkR : m62Curvature F c s y ≤ R + 1 := by
      nlinarith only [curvature_sq F c s y, hqR,
        sq_nonneg (m62Curvature F c s y - 1)]
    have hsum : q y s + m62Curvature F c s y ≤ 2 * R + 1 := by
      linarith only [hqR, hkR]
    have hq2 : q y s ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (hq y s) hqR 2
    change deriv (q y) s ≤ m62ArcSecondDerivative F c s (fun z => q z s) y -
      2 * (F.metric s).inner (c y s) (m62SpatialNormalDerivative F c s y)
        (m62SpatialNormalDerivative F c s y) + 2 * q y s ^ 2 +
        m62C0 K K K * (q y s + m62Curvature F c s y) at hraw
    dsimp only [D0]
    nlinarith only [hraw, hsplit, hq2, mul_le_mul_of_nonneg_left hsum hC0]
  have hqSmooth : ContDiffOn ℝ ∞ (Function.uncurry q) (univ ×ˢ Ioo a b) :=
    curvatureSquared_contDiffOn F c hc
  have hbetaSmooth : ContDiffOn ℝ ∞ (Function.uncurry beta) (univ ×ˢ Ioo a b) :=
    m63CurvatureJetSquared_joint_contDiff F c hc 1
  have hqs (s : ℝ) (hs : s ∈ Ioo a b) : ContDiff ℝ ∞ (fun y => q y s) :=
    hqSmooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, hs⟩)
  have hbetas (s : ℝ) (hs : s ∈ Ioo a b) : ContDiff ℝ ∞ (fun y => beta y s) :=
    hbetaSmooth.comp_contDiff (contDiff_id.prodMk contDiff_const)
      (fun _ => ⟨mem_univ _, hs⟩)
  have hvs (s : ℝ) (hs : s ∈ Ioo a b) :
      ContDiff ℝ ∞ (fun y => (curveSpeed F c s y)⁻¹) :=
    ((speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hs⟩)).inv
        (fun y => (speed_pos F c hc (Ioo_subset_Icc_self hs) y).ne')
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hqt (y s : ℝ) (hs : s ∈ Ioo a b) : DifferentiableAt ℝ (q y) s :=
    ((hqSmooth.contDiffAt (hopen.mem_nhds ⟨mem_univ y, hs⟩)).comp s
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hbetat (y s : ℝ) (hs : s ∈ Ioo a b) : DifferentiableAt ℝ (beta y) s :=
    ((hbetaSmooth.contDiffAt (hopen.mem_nhds ⟨mem_univ y, hs⟩)).comp s
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change ∀ x t, t ∈ Ioo a b → t - a ≤ 1 → beta x t ≤ (lambda * R + D) / (t - a)
  intro x t ht hshort
  have hrestart (sigma : ℝ) (hsigma : sigma ∈ Ioo a t) :
      (t - sigma) * beta x t ≤ lambda * R + D * (t - sigma) := by
    let Q : ℝ → ℝ → ℝ := fun y s => (s - sigma) * beta y s + lambda * q y s
    let V : ℝ → ℝ → ℝ := fun y s => beta y s + (s - sigma) * deriv (beta y) s +
      lambda * deriv (q y) s
    have hclosed (s : ℝ) (hs : s ∈ Icc sigma t) : s ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hsigma.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hinner (s : ℝ) (hs : s ∈ Ioo sigma t) : s ∈ Ioo a b :=
      hclosed s (Ioo_subset_Icc_self hs)
    have hQjoint : ContDiffOn ℝ ∞ (Function.uncurry Q) (univ ×ˢ Ioo a b) :=
      ((contDiff_snd.sub contDiff_const).contDiffOn.mul hbetaSmooth).add
        (contDiffOn_const.mul hqSmooth)
    have hQs (s : ℝ) (hs : s ∈ Ioo a b) : ContDiff ℝ ∞ (fun y => Q y s) :=
      (contDiff_const.mul (hbetas s hs)).add (contDiff_const.mul (hqs s hs))
    have hQtime (y s : ℝ) (hs : s ∈ Ioo sigma t) : HasDerivAt (Q y) (V y s) s := by
      have hd : HasDerivAt (Q y)
          (1 * beta y s + (s - sigma) * deriv (beta y) s + lambda * deriv (q y) s) s :=
        (((hasDerivAt_id s).sub_const sigma).mul
          (hbetat y s (hinner s hs)).hasDerivAt).add
            ((hqt y s (hinner s hs)).hasDerivAt.const_mul lambda)
      simpa only [one_mul] using hd
    have hQspace (y s : ℝ) (hs : s ∈ Ioo a b) :
        m62ArcSecondDerivative F c s (fun z => Q z s) y =
          (s - sigma) * m62ArcSecondDerivative F c s (fun z => beta z s) y +
            lambda * m62ArcSecondDerivative F c s (fun z => q z s) y := by
      have hba : ContDiff ℝ ∞ (m62ArcDerivative F c s (fun z => beta z s)) :=
        (hvs s hs).mul (contDiff_infty_iff_deriv.mp (hbetas s hs)).2
      have hqa : ContDiff ℝ ∞ (m62ArcDerivative F c s (fun z => q z s)) :=
        (hvs s hs).mul (contDiff_infty_iff_deriv.mp (hqs s hs)).2
      have hfirst (z : ℝ) : m62ArcDerivative F c s (fun w => Q w s) z =
          (s - sigma) * m62ArcDerivative F c s (fun w => beta w s) z +
            lambda * m62ArcDerivative F c s (fun w => q w s) z := by
        have hd : HasDerivAt (fun w => Q w s)
            ((s - sigma) * deriv (fun w => beta w s) z +
              lambda * deriv (fun w => q w s) z) z :=
          (((hbetas s hs).differentiable (by simp) z).hasDerivAt.const_mul (s - sigma)).add
            (((hqs s hs).differentiable (by simp) z).hasDerivAt.const_mul lambda)
        rw [m62ArcDerivative, hd.deriv]
        dsimp only [m62ArcDerivative]
        ring
      have hd : HasDerivAt
          (fun z => (s - sigma) * m62ArcDerivative F c s (fun w => beta w s) z +
            lambda * m62ArcDerivative F c s (fun w => q w s) z)
          ((s - sigma) * deriv (m62ArcDerivative F c s (fun w => beta w s)) y +
            lambda * deriv (m62ArcDerivative F c s (fun w => q w s)) y) y :=
        ((hba.differentiable (by simp) y).hasDerivAt.const_mul (s - sigma)).add
          ((hqa.differentiable (by simp) y).hasDerivAt.const_mul lambda)
      change m62ArcDerivative F c s
        (fun z => m62ArcDerivative F c s (fun w => Q w s) z) y = _
      rw [show (fun z => m62ArcDerivative F c s (fun w => Q w s) z) =
        (fun z => (s - sigma) * m62ArcDerivative F c s (fun w => beta w s) z +
          lambda * m62ArcDerivative F c s (fun w => q w s) z) from funext hfirst]
      rw [m62ArcDerivative, hd.deriv]
      dsimp only [m62ArcSecondDerivative, m62ArcDerivative]
      ring
    have hcompare := Poincare.Parabolic.periodic_le_affine_mul_exp_of_weighted_parabolic_le
      (F := Q) (V := V) (w := fun y s => (curveSpeed F c s y)⁻¹)
      (B := fun _ _ => 0) (p := curvePeriod) (K := 0) (d := D) (R := lambda * R)
      (by unfold curvePeriod; positivity) hsigma.2 (by norm_num) hD
      (hQjoint.continuousOn.mono (fun z hz => ⟨hz.1, hclosed z.2 hz.2⟩))
      (fun s hs y => by
        have hb := m63CurvatureJetSquared_periodic F c hc 1 (hclosed s hs) y
        have hqper := m63CurvatureJetSquared_periodic F c hc 0 (hclosed s hs) y
        change beta (y + curvePeriod) s = beta y s at hb
        change q (y + curvePeriod) s = q y s at hqper
        dsimp only [Q]
        rw [hb, hqper])
      hQtime
      (fun y s hs => (hvs s (hinner s hs)).differentiable (by simp) y)
      (fun y s hs => (contDiff_infty_iff_deriv.mp (hQs s (hinner s hs))).2.differentiable
        (by simp) y)
      (fun y s hs => by
        have hsn : 0 ≤ s - sigma := sub_nonneg.mpr hs.1.le
        have hsone : s - sigma ≤ 1 := by linarith only [hs.2, hsigma.1, hshort]
        have hbm := mul_le_mul_of_nonneg_left (hbetaPDE y s (hinner s hs)) hsn
        have hqm := mul_le_mul_of_nonneg_left (hqPDE y s (hinner s hs)) hlambda
        have hcoef : 1 + (s - sigma) * C - 2 * lambda ≤ 0 := by
          dsimp only [lambda]
          nlinarith only [mul_le_mul_of_nonneg_right hsone hC, hC]
        have hbneg := mul_nonpos_of_nonpos_of_nonneg hcoef (hbeta y s)
        have hcneg := mul_nonneg hsn (hchi y s)
        have hctime := mul_le_mul_of_nonneg_right hsone hC
        simp only [zero_mul, add_zero]
        change V y s ≤ m62ArcSecondDerivative F c s (fun z => Q z s) y + D
        rw [hQspace y s (hinner s hs)]
        dsimp only [V, D]
        nlinarith only [hbm, hqm, hbneg, hcneg, hctime])
      (fun y => by
        dsimp only [Q]
        simp only [sub_self, zero_mul, zero_add]
        exact mul_le_mul_of_nonneg_left (hcurv sigma (hclosed sigma ⟨le_rfl, hsigma.2.le⟩) y)
          hlambda)
    have h := hcompare x t ⟨hsigma.2.le, le_rfl⟩
    simp only [zero_mul, Real.exp_zero, mul_one] at h
    have hnon := mul_nonneg hlambda (hq x t)
    change (t - sigma) * beta x t + lambda * q x t ≤ lambda * R + D * (t - sigma) at h
    linarith only [h, hnon]
  have hevent : ∀ᶠ sigma in 𝓝[>] a,
      (t - sigma) * beta x t ≤ lambda * R + D * (t - sigma) := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with sigma hsigma
    exact hrestart sigma hsigma
  have hleft : Tendsto (fun sigma => (t - sigma) * beta x t) (𝓝[>] a)
      (𝓝 ((t - a) * beta x t)) :=
    (show Continuous (fun sigma : ℝ => (t - sigma) * beta x t) by fun_prop).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun sigma => lambda * R + D * (t - sigma)) (𝓝[>] a)
      (𝓝 (lambda * R + D * (t - a))) :=
    (show Continuous (fun sigma : ℝ => lambda * R + D * (t - sigma)) by
      fun_prop).continuousAt.tendsto |>.mono_left nhdsWithin_le_nhds
  have hlimit := le_of_tendsto_of_tendsto hleft hright hevent
  apply (le_div_iff₀ (sub_pos.mpr ht.1)).mpr
  nlinarith only [hlimit, mul_le_mul_of_nonneg_left hshort hD]




theorem m63Exists_boundedCurvature_firstJet_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
      (∀ s ∈ Ioo a b, ∀ y, m62CurvatureSquared F c s y ≤ R) →
      ∀ x t, t ∈ Ioo a b → t - a ≤ 1 →
        m63CurvatureJetSquared F c 1 t x ≤ C0 / (t - a) := by
  obtain ⟨K, hK, hBounds, hRiemann, hSecond⟩ := m63Exists_firstJet_ambient_bounds F hcompact
  let C := 14 * R + 10 * K + 1 + 4 * R ^ 3 + 2 * R * K * (7 * R + 6) +
    (K * (46 * R + 32)) ^ 2
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hD0 : 0 ≤ D0 := by dsimp only [D0]; positivity
  refine ⟨(1 + C) * R + (C + (1 + C) * D0), by positivity, ?_⟩
  intro c hc hcurv
  exact m63FirstJetSquared_bound_of_curvature_bound F c hc hK hR hBounds hRiemann hSecond hcurv

end PoincareConjecture
