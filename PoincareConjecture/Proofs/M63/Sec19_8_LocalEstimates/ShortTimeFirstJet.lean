import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.BoundedCurvatureFirstJet

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63FirstJetSquared_dissipation_split [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hcurv : m62CurvatureSquared F c t x ≤ R)
    (hRiemann : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation (c x t) v| ≤ K)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K) :
    let A := 14 * R + 10 * K + 1
    let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
    deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x ≤
      -m63CurvatureJetSquared F c 2 t x + A * m63CurvatureJetSquared F c 1 t x + G := by
  let p := c x t
  let g := F.metric t
  let D := F.connection t
  let Rm := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let J := D.covariantTensorDerivative Rm
  let S := spatialUnitTangent F c t x
  let H := m63CurvatureJet F c 0 t x
  let B := m63CurvatureJet F c 1 t x
  let V := m63CurvatureJet F c 2 t x
  let k := m62Curvature F c t x
  let q := m62CurvatureSquared F c t x
  let beta := m63CurvatureJetSquared F c 1 t x
  let chi := m63CurvatureJetSquared F c 2 t x
  let u := g.tangentNorm p B
  let w := g.tangentNorm p V
  let N := g.inner p H B
  let r := m62TangentRicci F c t
  let E := J p ![S, H, S, B, S] + Rm p ![B, S, B, S] +
    2 * Rm p ![H, S, B, H] - 2 * U p ![S, S, S, B] +
    U p ![S, B, S, S] - 3 * T p ![H, S, B] -
    3 * T p ![S, H, B] + 3 * T p ![B, S, H]
  let L := deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
    m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x
  change L ≤ -chi + (14 * R + 10 * K + 1) * beta +
    (4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2)
  have ht' := Ioo_subset_Icc_self ht
  have hS : g.tangentNorm p S = 1 := unitTangent_norm F c hc ht' x
  have hH : g.tangentNorm p H = k := rfl
  have hB : g.tangentNorm p B = u := rfl
  have hV : g.tangentNorm p V = w := rfl
  have hk : 0 ≤ k := curvature_nonneg F c t x
  have hq : 0 ≤ q := curvatureSquared_nonneg F c t x
  have hbeta : 0 ≤ beta := (g.toRiemannianMetric.toCore p).re_inner_nonneg B
  have hchi : 0 ≤ chi := (g.toRiemannianMetric.toCore p).re_inner_nonneg V
  have hun : 0 ≤ u := Real.sqrt_nonneg _
  have hkq : k ^ 2 = q := curvature_sq F c t x
  have hu : u ^ 2 = beta := Real.sq_sqrt hbeta
  have hw : w ^ 2 = chi := Real.sq_sqrt hchi
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hN : |N| ≤ k * u := by
    change |inner ℝ H B| ≤ k * u
    simpa only [hn, hH, hB] using abs_real_inner_le_norm H B
  have hNsq : N ^ 2 ≤ q * beta := by
    change (inner ℝ H B) ^ 2 ≤ inner ℝ H H * inner ℝ B B
    simpa only [pow_two] using real_inner_mul_inner_self_le H B
  have hVH : |g.inner p V H| ≤ w * k := by
    change |inner ℝ V H| ≤ w * k
    simpa only [hn, hV, hH] using abs_real_inner_le_norm V H
  have hRic (Y Z : TangentSpace (𝓡 n) p) :
      |D.ricci p Y Z| ≤ K * g.tangentNorm p Y * g.tangentNorm p Z := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p
      (fun v hv => hBounds.ricci t ht' p (v 0) (v 1) (hv 0) (hv 1)) ![Y, Z]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, mul_assoc] using h
  have hRicBB : |D.ricci p B B| ≤ K * beta := by
    simpa only [hB, mul_assoc, ← pow_two, hu] using hRic B B
  have hr : |r x| ≤ K := by
    change |D.ricci p S S| ≤ K
    simpa only [hS, mul_one] using hRic S S
  have harc := m63TangentRicci_arc_abs_bounds F c hc hK hBounds ht x hSecond
  change |m62ArcDerivative F c t r x| ≤ K * (1 + 2 * k) ∧
    |m62ArcSecondDerivative F c t r x| ≤ K * (1 + 5 * k + 2 * u + 2 * q) at harc
  have hE := m63FirstJet_ambient_abs_bound F c hc hK hBounds ht x hRiemann hSecond
  change |E| ≤ K * beta + K * (2 * q + 10 * k + 3) * u at hE
  have heq := m63FirstJetSquared_evolution F c hc ht x
  change L = -2 * chi - 2 * D.ricci p B B + (2 * q + 6 * r x) * beta +
    12 * N ^ 2 + 6 * m62ArcDerivative F c t r x * N -
    4 * q * g.inner p V H - 2 * q * m62ArcSecondDerivative F c t r x + 2 * E at heq
  have hRicTerm : -2 * D.ricci p B B ≤ 2 * K * beta := by
    nlinarith only [(abs_le.mp hRicBB).1]
  have hrTerm : (2 * q + 6 * r x) * beta ≤ (2 * q + 6 * K) * beta := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hr).2 hbeta
    nlinarith only [h]
  have hcross : 6 * m62ArcDerivative F c t r x * N ≤
      6 * K * k * u + 12 * K * q * u := by
    have hmul : |m62ArcDerivative F c t r x * N| ≤ K * (1 + 2 * k) * (k * u) := by
      rw [abs_mul]
      exact mul_le_mul harc.1 hN (abs_nonneg _) (by positivity)
    calc
      _ ≤ 6 * (K * (1 + 2 * k) * (k * u)) := by
        nlinarith only [le_abs_self (m62ArcDerivative F c t r x * N), hmul]
      _ = _ := by rw [← hkq]; ring
  have hVTerm : -4 * q * g.inner p V H ≤ 4 * q * k * w := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hVH).1 (show 0 ≤ 4 * q by positivity)
    nlinarith only [h]
  have hsecondTerm : -2 * q * m62ArcSecondDerivative F c t r x ≤
      2 * q * K * (1 + 5 * k + 2 * u + 2 * q) := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp harc.2).1
      (show 0 ≤ 2 * q by positivity)
    nlinarith only [h]
  have hraw : L ≤ -2 * chi + (14 * q + 10 * K) * beta +
      K * (20 * q + 26 * k + 6) * u + 4 * q * k * w +
      2 * q * K * (1 + 5 * k + 2 * q) := by
    nlinarith only [heq, hRicTerm, hrTerm, hNsq, hcross, hVTerm,
      hsecondTerm, (abs_le.mp hE).2]
  have hqR : q ≤ R := hcurv
  have hkR : k ≤ R + 1 := by
    nlinarith only [hkq, hqR, sq_nonneg (k - 1)]
  have hq3 : q ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hq hqR 3
  have hYoung : 4 * q * k * w ≤ chi + 4 * q ^ 3 := by
    have hs : 0 ≤ 4 * q ^ 3 - 4 * q * k * w + chi := by
      calc
        _ = (2 * q * k - w) ^ 2 := by rw [← hkq, ← hw]; ring
        _ ≥ 0 := sq_nonneg _
    linarith only [hs]
  let A := 14 * R + 10 * K + 1
  let D0 := K * (46 * R + 32)
  let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + D0 ^ 2
  have hcoef : (14 * q + 10 * K) * beta ≤ (14 * R + 10 * K) * beta := by
    exact mul_le_mul_of_nonneg_right (by linarith only [hqR]) hbeta
  have hlinear : K * (20 * q + 26 * k + 6) * u ≤ D0 * u := by
    apply mul_le_mul_of_nonneg_right _ hun
    apply mul_le_mul_of_nonneg_left _ hK
    linarith only [hqR, hkR]
  have hconstant : 2 * q * K * (1 + 5 * k + 2 * q) ≤
      2 * R * K * (7 * R + 6) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqR (by norm_num)) hK
    · linarith only [hkR, hqR]
    · positivity
    · positivity
  have hlinearYoung : D0 * u ≤ beta + D0 ^ 2 := by
    nlinarith only [sq_nonneg (u - D0), hu, hbeta, sq_nonneg D0]
  have hbound : L ≤ -chi + A * beta + G := by
    dsimp only [A, G]
    nlinarith only [hraw, hYoung, hq3, hcoef, hlinear, hconstant, hlinearYoung]
  exact hbound

theorem m63FirstJetSquared_short_time_bound [T2Space M]
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
    (hcurv : ∀ s ∈ Ioo a b, ∀ y, m62CurvatureSquared F c s y ≤ R)
    {H : ℝ} (hH : 0 ≤ H) :
    let A := 14 * R + 10 * K + 1
    let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
    let lambda := 1 + A * H
    let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
    let D := H * G + lambda * D0
    ∀ x t, t ∈ Ioo a b → t - a ≤ H →
      m63CurvatureJetSquared F c 1 t x ≤ lambda * R / (t - a) + D := by
  let A := 14 * R + 10 * K + 1
  let G := 4 * R ^ 3 + 2 * R * K * (7 * R + 6) + (K * (46 * R + 32)) ^ 2
  let lambda := 1 + A * H
  let D0 := 4 * R ^ 2 + m62C0 K K K * (2 * R + 1)
  let D := H * G + lambda * D0
  let q : ℝ → ℝ → ℝ := fun y s => m62CurvatureSquared F c s y
  let beta : ℝ → ℝ → ℝ := fun y s => m63CurvatureJetSquared F c 1 s y
  let chi : ℝ → ℝ → ℝ := fun y s => m63CurvatureJetSquared F c 2 s y
  have hC0 : 0 ≤ m62C0 K K K := by unfold m62C0; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
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
        -chi y s + A * beta y s + G :=
    m63FirstJetSquared_dissipation_split F c hc hK hR hBounds hs y (hcurv s hs y)
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
  change ∀ x t, t ∈ Ioo a b → t - a ≤ H → beta x t ≤ lambda * R / (t - a) + D
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
        have hshorizon : s - sigma ≤ H := by linarith only [hs.2, hsigma.1, hshort]
        have hbm := mul_le_mul_of_nonneg_left (hbetaPDE y s (hinner s hs)) hsn
        have hqm := mul_le_mul_of_nonneg_left (hqPDE y s (hinner s hs)) hlambda
        have hcoef : 1 + (s - sigma) * A - 2 * lambda ≤ 0 := by
          dsimp only [lambda]
          nlinarith only [mul_le_mul_of_nonneg_right hshorizon hA, mul_nonneg hA hH]
        have hbneg := mul_nonpos_of_nonpos_of_nonneg hcoef (hbeta y s)
        have hcneg := mul_nonneg hsn (hchi y s)
        have hforcing := mul_le_mul_of_nonneg_right hshorizon hG
        simp only [zero_mul, add_zero]
        change V y s ≤ m62ArcSecondDerivative F c s (fun z => Q z s) y + D
        rw [hQspace y s (hinner s hs)]
        dsimp only [V, D]
        nlinarith only [hbm, hqm, hbneg, hcneg, hforcing])
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
  calc
    beta x t ≤ (lambda * R + D * (t - a)) / (t - a) :=
      (le_div_iff₀ (sub_pos.mpr ht.1)).mpr (by simpa only [mul_comm] using hlimit)
    _ = lambda * R / (t - a) + D := by
      rw [add_div, mul_div_cancel_right₀ D (sub_pos.mpr ht.1).ne']

end PoincareConjecture
