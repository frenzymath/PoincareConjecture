import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetCrossPair
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetAmbientDerivativeBound
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ThirdTangentRicciBound
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetTermBounds
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetErrorIdentities

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option maxHeartbeats 800000 in

theorem m63SecondJetSquared_dissipation [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R B : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hcurv : m63CurvatureJetSquared F c 0 t x ≤ R)
    (hfirst : m63CurvatureJetSquared F c 1 t x ≤ B)
    (hRiemann : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation (c x t) v| ≤ K)
    (hRiemannSecond : ∀ v : Fin 6 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).riemannEvaluation) (c x t) v| ≤ K)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K)
    (hThird : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            ((F.connection t).covariantTensorDerivative
              (F.connection t).ricciEvaluation)) (c x t) v| ≤ K) :
    let P0 := K * (4 + 32 * (R + 1) + 27 * (B + 1) + 46 * R +
      33 * (R + 1) * (B + 1) + 10 * (R + 1) ^ 3) + 20 * (R + 1) * B
    let C2 := 16 * K + 28 * R + 12 * (B + 1) + 1 + P0 ^ 2
    deriv (fun s => m63CurvatureJetSquared F c 2 s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 2 t) x ≤
      -m63CurvatureJetSquared F c 3 t x +
        C2 * m63CurvatureJetSquared F c 2 t x + C2 := by
  let g := F.metric t
  let D := F.connection t
  let p := c x t
  let Rm := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let R1 := D.covariantTensorDerivative Rm
  let V : ℕ → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2)
    | 0, z => spatialUnitTangent F c z.2 z.1
    | i + 1, z => m63CurvatureJet F c i z.2 z.1
  let P : ℕ → ℕ → ℝ → ℝ := fun i j y =>
    g.inner (c y t) (V i (y, t)) (V j (y, t))
  let q := m62CurvatureSquared F c t
  let r := m62TangentRicci F c t
  let A := fun y => r y + q y
  let As := m62ArcDerivative F c t A
  let Ass := m62ArcDerivative F c t As
  let Asss := m62ArcDerivative F c t Ass
  let E := fun (i : ℕ) y =>
    let S := V 0 (y, t)
    let H := V 1 (y, t)
    let J1 := V 2 (y, t)
    let Z := V (i + 1) (y, t)
    R1 (c y t) ![S, H, S, Z, S] + Rm (c y t) ![J1, S, Z, S] +
      2 * Rm (c y t) ![H, S, Z, H] - 2 * U (c y t) ![S, S, S, Z] +
      U (c y t) ![S, Z, S, S] - 3 * T (c y t) ![H, S, Z] -
      3 * T (c y t) ![S, H, Z] + 3 * T (c y t) ![Z, S, H]
  let Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := fun z =>
    rampHorizontalCovariantDerivative D (fun s => c z.1 s)
      (fun s => m63CurvatureJet F c 1 s z.1) z.2
  let L := fun y => g.inner (c y t) (Y (y, t)) (V 3 (y, t))
  let comm := Rm p ![V 1 (x, t), V 0 (x, t), V 3 (x, t), V 2 (x, t)] -
    T p ![V 0 (x, t), V 2 (x, t), V 3 (x, t)] -
    T p ![V 2 (x, t), V 0 (x, t), V 3 (x, t)] +
    T p ![V 3 (x, t), V 0 (x, t), V 2 (x, t)]
  let E2 := m62ArcDerivative F c t (E 2) x - E 3 x + comm
  let N := fun i => g.tangentNorm p (V i (x, t))
  let k := N 1
  let u := N 2
  let w := N 3
  let z := N 4
  have hV (i : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, V i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases i with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ i => exact M63.curvatureJet_joint_contMDiff F c hc i
  have hrec (i : ℕ) (y : ℝ) :
      m62SpatialDerivative F c t (fun s => V i (s, t)) y = V (i + 1) (y, t) := by
    cases i <;> rfl
  have hP (i j : ℕ) : ContDiff ℝ ∞ (P i j) :=
    (metric_pairing_contDiffOn F c hc.joint_smooth (V i) (V j) (hV i) (hV j)).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hsym (i j : ℕ) (y : ℝ) : P i j y = P j i y := g.symm _ _ _
  have hpair (i j : ℕ) (y : ℝ) : m62ArcDerivative F c t (P i j) y =
      P (i + 1) j y + P i (j + 1) y := by
    simpa only [hrec] using
      m63ArcDerivative_metric_pairing F c hc (V i) (V j) (hV i) (hV j) ht y
  have hA : ContDiff ℝ ∞ A :=
    (normalization_coefficient_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hq : ContDiff ℝ ∞ q := hP 1 1
  have hr : ContDiff ℝ ∞ r := by
    have heq : (fun y => A y - q y) = r := by funext y; dsimp only [A]; ring
    exact heq ▸ hA.sub hq
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hsmooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (m62ArcDerivative F c t f) :=
    (hv.inv (fun y => (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne')).mul
      (contDiff_infty_iff_deriv.mp hf).2
  have hAs := hsmooth hA
  have hAss := hsmooth hAs
  have hadd {f h : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (y : ℝ) :
      m62ArcDerivative F c t (fun s => f s + h s) y =
        m62ArcDerivative F c t f y + m62ArcDerivative F c t h y := by
    rw [m62ArcDerivative, ((hf.differentiable (by simp) y).hasDerivAt.fun_add
      (hh.differentiable (by simp) y).hasDerivAt).deriv]
    dsimp only [m62ArcDerivative]
    ring
  have hscale {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (d y : ℝ) :
      m62ArcDerivative F c t (fun s => d * f s) y =
        d * m62ArcDerivative F c t f y := by
    rw [m62ArcDerivative, ((hf.differentiable (by simp) y).hasDerivAt.const_mul d).deriv]
    dsimp only [m62ArcDerivative]
    ring
  have hq1 (y : ℝ) : m62ArcDerivative F c t q y = 2 * P 1 2 y := by
    change m62ArcDerivative F c t (P 1 1) y = _
    rw [hpair 1 1 y, hsym 2 1 y]
    ring
  have hq2 (y : ℝ) : m62ArcSecondDerivative F c t q y =
      2 * P 1 3 y + 2 * P 2 2 y := by
    change m62ArcDerivative F c t (m62ArcDerivative F c t q) y = _
    rw [show m62ArcDerivative F c t q = (fun s => 2 * P 1 2 s) from funext hq1,
      hscale (hP 1 2), hpair 1 2 y]
    ring
  have hq3 : m62ArcDerivative F c t (m62ArcSecondDerivative F c t q) x =
      2 * P 1 4 x + 6 * P 2 3 x := by
    rw [show m62ArcSecondDerivative F c t q =
        (fun y => 2 * P 1 3 y + 2 * P 2 2 y) from funext hq2,
      hadd (contDiff_const.mul (hP 1 3)) (contDiff_const.mul (hP 2 2)),
      hscale (hP 1 3), hscale (hP 2 2), hpair 1 3 x, hpair 2 2 x, hsym 3 2 x]
    ring
  have hsplit1 : As = fun y => m62ArcDerivative F c t r y +
      m62ArcDerivative F c t q y := funext fun y => hadd hr hq y
  have hsplit2 : Ass = fun y => m62ArcSecondDerivative F c t r y +
      m62ArcSecondDerivative F c t q y := by
    dsimp only [Ass]
    rw [hsplit1]
    exact funext fun y => hadd (hsmooth hr) (hsmooth hq) y
  have hsplit3 : Asss x = m62ArcDerivative F c t (m62ArcSecondDerivative F c t r) x +
      m62ArcDerivative F c t (m62ArcSecondDerivative F c t q) x := by
    dsimp only [Asss]
    rw [hsplit2]
    exact hadd (hsmooth (hsmooth hr)) (hsmooth (hsmooth hq)) x
  have hE := m63FirstJetAmbientPair_jet_derivative_bound F c hc 2 hK hBounds ht x
    hRiemann hRiemannSecond hSecond hThird
  change DifferentiableAt ℝ (E 2) x ∧
    |m62ArcDerivative F c t (E 2) x - E 3 x| ≤
      K * (w + 11 * u + 19 * k + 14 * k ^ 2 + 6 * k * u + 2 * k ^ 3 + 3) * w at hE
  have hidentity (y : ℝ) : L y = P 4 3 y + 3 * A y * P 2 3 y +
      3 * As y * P 1 3 y + Ass y * P 0 3 y + E 2 y :=
    m63FirstJet_time_jet_pair F c hc 2 ht y
  have htest : g.inner p (Y (x, t)) (V 4 (x, t)) = P 4 4 x +
      3 * A x * P 2 4 x + 3 * As x * P 1 4 x + Ass x * P 0 4 x + E 3 x :=
    m63FirstJet_time_jet_pair F c hc 3 ht x
  have hRHS : m62ArcDerivative F c t
      (fun y => P 4 3 y + 3 * A y * P 2 3 y + 3 * As y * P 1 3 y +
        Ass y * P 0 3 y + E 2 y) x =
      m62ArcDerivative F c t (P 4 3) x + 3 * As x * P 2 3 x +
        3 * A x * m62ArcDerivative F c t (P 2 3) x +
        3 * Ass x * P 1 3 x + 3 * As x * m62ArcDerivative F c t (P 1 3) x +
        Asss x * P 0 3 x + Ass x * m62ArcDerivative F c t (P 0 3) x +
        m62ArcDerivative F c t (E 2) x := by
    have hd : HasDerivAt
        (fun y => P 4 3 y + 3 * A y * P 2 3 y + 3 * As y * P 1 3 y +
          Ass y * P 0 3 y + E 2 y)
        (deriv (P 4 3) x + (3 * deriv A x * P 2 3 x + 3 * A x * deriv (P 2 3) x) +
          (3 * deriv As x * P 1 3 x + 3 * As x * deriv (P 1 3) x) +
          (deriv Ass x * P 0 3 x + Ass x * deriv (P 0 3) x) + deriv (E 2) x) x :=
      (((((hP 4 3).differentiable (by simp) x).hasDerivAt.add
      (((hA.differentiable (by simp) x).hasDerivAt.const_mul 3).mul
        ((hP 2 3).differentiable (by simp) x).hasDerivAt)).add
      (((hAs.differentiable (by simp) x).hasDerivAt.const_mul 3).mul
        ((hP 1 3).differentiable (by simp) x).hasDerivAt)).add
      ((hAss.differentiable (by simp) x).hasDerivAt.mul
        ((hP 0 3).differentiable (by simp) x).hasDerivAt)).add hE.1.hasDerivAt
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [As, Ass, Asss, m62ArcDerivative]
    ring
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hY := m63FixedPullback_time_joint_contMDiff D c (V 2) hopen hc.joint_smooth (hV 2)
  have hL := m63ArcDerivative_metric_pairing F c hc Y (V 3) hY (hV 3) ht x
  change m62ArcDerivative F c t L x =
    g.inner p (m62SpatialDerivative F c t (fun y => Y (y, t)) x) (V 3 (x, t)) +
      g.inner p (Y (x, t)) (V 4 (x, t)) at hL
  rw [show L = (fun y => P 4 3 y + 3 * A y * P 2 3 y +
      3 * As y * P 1 3 y + Ass y * P 0 3 y + E 2 y) from funext hidentity,
    hRHS, hpair 4 3 x, hpair 2 3 x, hpair 1 3 x, hpair 0 3 x, htest] at hL
  have hcomm := m63SpatialDerivative_time_commutator_pair F c hc (V 2) (hV 2) ht x
    (V 3 (x, t))
  change g.inner p
      (rampHorizontalCovariantDerivative D (fun s => c x s)
        (fun s => m63CurvatureJet F c 2 s x) t) (V 3 (x, t)) =
    g.inner p (m62SpatialDerivative F c t (fun y => Y (y, t)) x) (V 3 (x, t)) +
      A x * P 3 3 x +
      Rm p ![V 1 (x, t), V 0 (x, t), V 3 (x, t), V 2 (x, t)] -
      T p ![V 0 (x, t), V 2 (x, t), V 3 (x, t)] -
      T p ![V 2 (x, t), V 0 (x, t), V 3 (x, t)] +
      T p ![V 3 (x, t), V 0 (x, t), V 2 (x, t)] at hcomm
  let Q := rampHorizontalCovariantDerivative D (fun s => c x s)
    (fun s => m63CurvatureJet F c 2 s x) t - V 5 (x, t)
  have hQ : g.inner p Q (V 3 (x, t)) = 4 * A x * P 3 3 x +
      6 * As x * P 2 3 x + 4 * Ass x * P 1 3 x + Asss x * P 0 3 x + E2 := by
    dsimp only [Q]
    simp only [map_sub, sub_apply]
    change _ - P 5 3 x = _
    dsimp only [E2, comm]
    linear_combination hcomm - hL
  have hN (i : ℕ) : 0 ≤ N i := Real.sqrt_nonneg _
  have hN0 : N 0 = 1 := unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hnorm0 : g.tangentNorm p (V 0 (x, t)) = 1 := hN0
  have hNsq (i : ℕ) : N i ^ 2 = P i i x :=
    Real.sq_sqrt ((g.toRiemannianMetric.toCore p).re_inner_nonneg (V i (x, t)))
  have hinner (i j : ℕ) : |P i j x| ≤ N i * N j := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
      rw [norm_eq_sqrt_real_inner]
      rfl
    change |inner ℝ (V i (x, t)) (V j (x, t))| ≤ _
    simpa only [hn] using abs_real_inner_le_norm (V i (x, t)) (V j (x, t))
  have hRic (Y Z : TangentSpace (𝓡 n) p) :
      |D.ricci p Y Z| ≤ K * g.tangentNorm p Y * g.tangentNorm p Z := by
    have h := tensor_abs_le_of_unit_bound g D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D) p
      (fun v hv => hBounds.ricci t (Ioo_subset_Icc_self ht) p
        (v 0) (v 1) (hv 0) (hv 1)) ![Y, Z]
    simpa [LeviCivitaData.ricciEvaluation, Fin.prod_univ_succ, mul_assoc] using h
  have hr0 : |r x| ≤ K := by
    have h := hRic (V 0 (x, t)) (V 0 (x, t))
    rw [hnorm0, mul_one, mul_one] at h
    simpa only [r, m62TangentRicci, D, p, V] using h
  have hr12 := m63TangentRicci_arc_abs_bounds F c hc hK hBounds ht x hSecond
  change |m62ArcDerivative F c t r x| ≤ K * (1 + 2 * k) ∧
    |m62ArcSecondDerivative F c t r x| ≤ K * (1 + 5 * k + 2 * u + 2 * q x) at hr12
  have hr3 := (m63TangentRicci_third_arc_bound F c hc hK hBounds ht x hSecond hThird).2
  change |m62ArcDerivative F c t (m62ArcSecondDerivative F c t r) x| ≤
    K * (1 + 9 * k + 7 * u + 12 * k ^ 2 + 6 * k * u + 2 * w) at hr3
  have hkq : k ^ 2 = q x := hNsq 1
  have hA0 : |A x| ≤ K + k ^ 2 := by
    apply (abs_add_le _ _).trans
    simpa only [← hkq, abs_of_nonneg (sq_nonneg k)] using
      add_le_add hr0 (le_refl (|q x|))
  have hA1 : |As x| ≤ K * (1 + 2 * k) + 2 * k * u := by
    rw [hsplit1]
    dsimp only
    rw [hq1 x]
    have hp : |2 * P 1 2 x| ≤ 2 * k * u := by
      simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
        using mul_le_mul_of_nonneg_left (hinner 1 2) (by norm_num : (0 : ℝ) ≤ 2)
    exact (abs_add_le _ _).trans (add_le_add hr12.1 hp)
  have hA2 : |Ass x| ≤ K * (1 + 5 * k + 2 * u + 2 * k ^ 2) +
      2 * k * w + 2 * u ^ 2 := by
    rw [hsplit2]
    dsimp only
    rw [hq2 x]
    have hp : |2 * P 1 3 x + 2 * P 2 2 x| ≤ 2 * k * w + 2 * u ^ 2 := by
      have h := abs_add_le (2 * P 1 3 x) (2 * P 2 2 x)
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
      nlinarith only [h, hinner 1 3, hinner 2 2]
    have h := (abs_add_le _ _).trans (add_le_add hr12.2 hp)
    simpa only [← hkq, add_assoc] using h
  have hA3 : |Asss x| ≤
      K * (1 + 9 * k + 7 * u + 12 * k ^ 2 + 6 * k * u + 2 * w) +
        2 * k * z + 6 * u * w := by
    rw [hsplit3, hq3]
    have hp : |2 * P 1 4 x + 6 * P 2 3 x| ≤ 2 * k * z + 6 * u * w := by
      have h := abs_add_le (2 * P 1 4 x) (6 * P 2 3 x)
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at h
      nlinarith only [h, hinner 1 4, hinner 2 3]
    simpa only [add_assoc] using (abs_add_le _ _).trans (add_le_add hr3 hp)
  have hRm := tensor_abs_le_of_unit_bound g Rm
    (M04.isSmoothCovariantTensor_riemannEvaluation D) p
    (hBounds.riemann t (Ioo_subset_Icc_self ht) p)
    ![V 1 (x, t), V 0 (x, t), V 3 (x, t), V 2 (x, t)]
  have hRm' : |Rm p ![V 1 (x, t), V 0 (x, t), V 3 (x, t), V 2 (x, t)]| ≤
      K * k * u * w := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, mul_one] at hRm
    change |Rm p ![V 1 (x, t), V 0 (x, t), V 3 (x, t), V 2 (x, t)]| ≤
      K * (k * (N 0 * (w * u))) at hRm
    simpa only [hN0, one_mul, mul_assoc, mul_comm u w] using hRm
  have hT (v : Fin 3 → TangentSpace (𝓡 n) p) :
      |T p v| ≤ K * ∏ i, g.tangentNorm p (v i) :=
    tensor_abs_le_of_unit_bound g T
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D
        (M04.isSmoothCovariantTensor_ricciEvaluation D)) p
      (hBounds.ricci_derivative t (Ioo_subset_Icc_self ht) p) v
  have hT1 : |T p ![V 0 (x, t), V 2 (x, t), V 3 (x, t)]| ≤ K * u * w := by
    simpa [Fin.prod_univ_succ, hnorm0, mul_assoc]
      using hT ![V 0 (x, t), V 2 (x, t), V 3 (x, t)]
  have hT2 : |T p ![V 2 (x, t), V 0 (x, t), V 3 (x, t)]| ≤ K * u * w := by
    simpa [Fin.prod_univ_succ, hnorm0, mul_assoc]
      using hT ![V 2 (x, t), V 0 (x, t), V 3 (x, t)]
  have hT3 : |T p ![V 3 (x, t), V 0 (x, t), V 2 (x, t)]| ≤ K * u * w := by
    simpa [Fin.prod_univ_succ, hnorm0, mul_assoc, mul_comm u w]
      using hT ![V 3 (x, t), V 0 (x, t), V 2 (x, t)]
  have hcomm_bound : |comm| ≤ K * (k * u + 3 * u) * w := by
    apply abs_le.mpr
    constructor
    · dsimp only [comm]
      nlinarith only [(abs_le.mp hRm').1, (abs_le.mp hT1).2,
        (abs_le.mp hT2).2, (abs_le.mp hT3).1]
    · dsimp only [comm]
      nlinarith only [(abs_le.mp hRm').2, (abs_le.mp hT1).1,
        (abs_le.mp hT2).1, (abs_le.mp hT3).2]
  have hE2 : |E2| ≤
      K * (w + 14 * u + 19 * k + 14 * k ^ 2 + 7 * k * u + 2 * k ^ 3 + 3) * w := by
    have h := (abs_add_le (m62ArcDerivative F c t (E 2) x - E 3 x) comm).trans
      (add_le_add hE.2 hcomm_bound)
    dsimp only [E2]
    nlinarith only [h]
  have hprod {f G : ℝ} (hf : |f| ≤ G) (i j : ℕ) :
      f * P i j x ≤ G * (N i * N j) := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul hf (hinner i j) (abs_nonneg _) ((abs_nonneg _).trans hf)
  have hrawQ : g.inner p Q (V 3 (x, t)) ≤
      2 * k * z * w + (7 * K + 12 * k ^ 2 + 6 * u) * w ^ 2 +
        (K * (4 + 32 * k + 27 * u + 46 * k ^ 2 + 33 * k * u + 10 * k ^ 3) +
          20 * k * u ^ 2) * w := by
    have h0 := hprod hA0 3 3
    have h1 := hprod hA1 2 3
    have h2 := hprod hA2 1 3
    have h3 := hprod hA3 0 3
    rw [hN0, one_mul] at h3
    rw [hQ]
    nlinarith only [h0, h1, h2, h3, (abs_le.mp hE2).2]
  let Pbound := K * (4 + 32 * k + 27 * u + 46 * k ^ 2 + 33 * k * u +
    10 * k ^ 3) + 20 * k * u ^ 2
  let P0 := K * (4 + 32 * (R + 1) + 27 * (B + 1) + 46 * R +
    33 * (R + 1) * (B + 1) + 10 * (R + 1) ^ 3) + 20 * (R + 1) * B
  let C2 := 16 * K + 28 * R + 12 * (B + 1) + 1 + P0 ^ 2
  have hk : 0 ≤ k := hN 1
  have hu : 0 ≤ u := hN 2
  have hw : 0 ≤ w := hN 3
  have hz : 0 ≤ z := hN 4
  have hkR : k ^ 2 ≤ R := by
    change N 1 ^ 2 ≤ R
    rw [hNsq 1]
    exact hcurv
  have huB : u ^ 2 ≤ B := by
    change N 2 ^ 2 ≤ B
    rw [hNsq 2]
    exact hfirst
  have hk1 : k ≤ R + 1 := by nlinarith only [hkR, sq_nonneg (k - 1)]
  have hu1 : u ≤ B + 1 := by nlinarith only [huB, sq_nonneg (u - 1)]
  have hP0 : 0 ≤ P0 := by dsimp only [P0]; positivity
  have hPb : 0 ≤ Pbound := by dsimp only [Pbound]; positivity
  have hPbound : Pbound ≤ P0 := by
    dsimp only [Pbound, P0]
    gcongr
  have hP2 : Pbound ^ 2 ≤ P0 ^ 2 := pow_le_pow_left₀ hPb hPbound 2
  have hRic33 : |D.ricci p (V 3 (x, t)) (V 3 (x, t))| ≤ K * w ^ 2 := by
    simpa only [mul_assoc, ← pow_two] using hRic (V 3 (x, t)) (V 3 (x, t))
  have hdiff := m63CurvatureJetSquared_diffusion_identity F c hc 2 ht x
  change deriv (fun s => m63CurvatureJetSquared F c 2 s x) t -
      m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 2 t) x =
    -2 * P 4 4 x - 2 * D.ricci p (V 3 (x, t)) (V 3 (x, t)) +
      2 * g.inner p Q (V 3 (x, t)) at hdiff
  have hraw : deriv (fun s => m63CurvatureJetSquared F c 2 s x) t -
      m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 2 t) x ≤
    -z ^ 2 + (16 * K + 28 * k ^ 2 + 12 * u + 1) * w ^ 2 + Pbound ^ 2 := by
    have hzsq : z ^ 2 = P 4 4 x := hNsq 4
    dsimp only [Pbound]
    nlinarith only [hdiff, hrawQ, (abs_le.mp hRic33).1, hzsq,
      sq_nonneg (z - 2 * k * w), sq_nonneg (w - Pbound)]
  have hcoef : (16 * K + 28 * k ^ 2 + 12 * u + 1) * w ^ 2 ≤
      (16 * K + 28 * R + 12 * (B + 1) + 1) * w ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith only [hkR, hu1]) (sq_nonneg w)
  change _ ≤ -P 4 4 x + C2 * P 3 3 x + C2
  rw [← hNsq 4, ← hNsq 3]
  dsimp only [C2]
  nlinarith only [hraw, hcoef, hP2, mul_nonneg (sq_nonneg P0) (sq_nonneg w), hK, hR, hB]

end PoincareConjecture
