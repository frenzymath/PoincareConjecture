import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.SmallTurningCurvatureBootstrap
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.C2SmallSubarcStability
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.ProductAmbientDerivativeBounds
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2EstimatesFromLocal












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture

open M62

variable {n : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : Real}




theorem m63CircleProduct_small_turning_curvature [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    (hM62 : M62CurveEvolutionTheory.{u}) (G : M63AmbientGeometry F)
    (L0 Theta0 : Real) (hL0 : 0 ≤ L0) (hTheta0 : 0 ≤ Theta0) :
    ∃ delta0 : Real, 0 < delta0 ∧ delta0 < 1 ∧
      ∀ circumference (hcirc : 0 < circumference), circumference < 1 →
      ∀ c : Real → Real → (G.product circumference hcirc).charts.Point,
        M63C2ShrinkingCurveOn (G.product circumference hcirc).flow c (Icc a b) →
        m62Length (G.product circumference hcirc).flow c a ≤ L0 →
        m62TotalCurvature (G.product circumference hcirc).flow c a ≤ Theta0 →
        ∀ s r : Real, a ≤ s → 0 < r → r ≤ 1 → s + delta0 * r ^ 2 ≤ b →
          r ≤ m62Length (G.product circumference hcirc).flow c s →
          M63SmallSubarcs (G.product circumference hcirc).flow c s r delta0 →
          ∀ t ∈ Ioc s (s + delta0 * r ^ 2), ∀ x,
            m63CurvatureJetSquared (G.product circumference hcirc).flow c 0 t x ≤
              2 / (t - s) := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  have hab : a < b := by
    obtain ⟨u, hu, v, hv, hne⟩ := F.nontrivial
    by_contra! h
    apply hne
    linarith only [hu.1, hu.2, hv.1, hv.2, h]
  obtain ⟨Kseq, hKseq, hTensor⟩ :=
    m63CircleProduct_uniform_curvature_derivative_bounds F hcompact
  obtain ⟨hK0, hK1, hK2⟩ := G.nonnegative
  let K := G.K0 + G.K1 + G.K2 + Kseq 1 + Kseq 2
  have hK : 0 ≤ K := by
    dsimp only [K]
    linarith only [hK0, hK1, hK2, hKseq 1, hKseq 2]
  have hK0K : G.K0 ≤ K := by
    dsimp only [K]
    linarith only [hK1, hK2, hKseq 1, hKseq 2]
  have hK1K : G.K1 ≤ K := by
    dsimp only [K]
    linarith only [hK0, hK2, hKseq 1, hKseq 2]
  have hK2K : G.K2 ≤ K := by
    dsimp only [K]
    linarith only [hK0, hK1, hKseq 1, hKseq 2]
  have hKr1 : Kseq 1 ≤ K := by
    dsimp only [K]
    linarith only [hK0, hK1, hK2, hKseq 2]
  have hKr2 : Kseq 2 ≤ K := by
    dsimp only [K]
    linarith only [hK0, hK1, hK2, hKseq 1]
  let Cbase := m62C1 G.K0 G.K1 G.K2 + G.K2
  have hCbase : 0 ≤ Cbase := by dsimp only [Cbase, m62C1, m62C0]; positivity
  let E := (L0 + Theta0) * Real.exp (Cbase * max (b - a) 0)
  have hE : 0 ≤ E := mul_nonneg (add_nonneg hL0 hTheta0) (Real.exp_pos _).le
  obtain ⟨psi, P1, P2, hP1, hP2, hpsi, hRange, hPlateau, hSupport, hFirst, hSecondPsi⟩ :=
    exists_m63ArcCutoff_profile
  let C1 := m62C1 K K K
  let D := (P2 + P1 * K * E + (C1 + K)) * E + C1 * E +
    2 * P1 * Real.sqrt 2 * E ^ 2
  let B := (272 + 17 * m62C0 K K K) * (114 + 10 * K) +
    2048 + 992 * K + 160000 * K ^ 2
  let h := min (1 / 4 : Real) (1 / (8 * Real.sqrt B + 1))
  have hh : 0 < h := lt_min (by norm_num) (by positivity)
  have hlossCont : Continuous (fun d : Real =>
      K * Real.exp K * d + 2 * Real.sqrt 2 * E * Real.sqrt d) := by fun_prop
  have hexpCont : Continuous (fun d : Real => Real.exp (K * d)) := by fun_prop
  have hturnCont : Continuous (fun d : Real => 2 * (d + D * Real.sqrt d)) := by fun_prop
  have hnearLoss : ∀ᶠ d in 𝓝 (0 : Real),
      K * Real.exp K * d + 2 * Real.sqrt 2 * E * Real.sqrt d < 1 / 20 :=
    hlossCont.continuousAt.eventually_lt continuousAt_const (by norm_num)
  have hnearExp : ∀ᶠ d in 𝓝 (0 : Real), Real.exp (K * d) < 3 / 2 :=
    hexpCont.continuousAt.eventually_lt continuousAt_const (by norm_num)
  have hnearTurn : ∀ᶠ d in 𝓝 (0 : Real), 2 * (d + D * Real.sqrt d) < h :=
    hturnCont.continuousAt.eventually_lt continuousAt_const (by simpa only [Real.sqrt_zero,
      mul_zero, add_zero] using hh)
  have hnear : ∀ᶠ d in 𝓝[>] (0 : Real),
      0 < d ∧ d < 1 ∧
      K * Real.exp K * d + 2 * Real.sqrt 2 * E * Real.sqrt d < 1 / 20 ∧
      Real.exp (K * d) < 3 / 2 ∧ 2 * (d + D * Real.sqrt d) < h := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (zero_lt_one : (0 : Real) < 1)).filter_mono nhdsWithin_le_nhds,
      hnearLoss.filter_mono nhdsWithin_le_nhds, hnearExp.filter_mono nhdsWithin_le_nhds,
      hnearTurn.filter_mono nhdsWithin_le_nhds] with d hd hd1 hl he ht
    exact ⟨hd, hd1, hl, he, ht⟩
  obtain ⟨delta, hd, hd1, hLoss, hExp, hTurn⟩ := hnear.exists
  let delta0 := delta / 8
  have hd0 : 0 < delta0 := div_pos hd (by norm_num)
  have hd0d : delta0 < delta := by dsimp only [delta0]; linarith only [hd]
  refine ⟨delta0, hd0, hd0d.trans hd1, ?_⟩
  intro circumference hcirc _hcirc1 c hc hLinitial hTinitial s r hs hr hr1 hEnd hLength hSmall
    t ht x
  let P := G.product circumference hcirc
  let : Fact (0 < circumference) := ⟨hcirc⟩
  let := P.charts.chartedSpace
  let : SecondCountableTopology P.charts.Point :=
    ChartedSpace.secondCountable_of_sigmaCompact
      (EuclideanSpace Real (Fin (n + 1))) P.charts.Point
  have hcompactP : IsCompact (univ : Set P.charts.Point) := isCompact_univ
  have hlocal := M63.localCurveTheory_of_compact P.flow hcompactP
  have hest := M63.c2_estimates_of_local hM62 P.flow hcompactP hlocal
    hK0 hK1 hK2 (G.product_bounds circumference hcirc) c hc hab
  have hBounds : CurveEvolutionAmbientBounds P.flow K K K := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu p v hv
      exact ((G.product_bounds circumference hcirc).riemann u hu p v hv).trans hK0K
    · intro u hu p v hv
      exact ((G.product_bounds circumference hcirc).ricci_derivative u hu p v hv).trans hK1K
    · intro u hu p v w hv hw
      exact ((G.product_bounds circumference hcirc).ricci u hu p v w hv hw).trans hK2K
  have hglobal (u : Real) (hu : u ∈ Icc a b) :
      m62Length P.flow c u ≤ E ∧ m62TotalCurvature P.flow c u ≤ E := by
    have hsum := hest.total_exponential a u ⟨le_rfl, hab.le⟩ hu hu.1
    have htheta : 0 ≤ m62TotalCurvature P.flow c u :=
      intervalIntegral.integral_nonneg_of_forall Real.two_pi_pos.le
        (fun y => mul_nonneg (Real.sqrt_nonneg _) (speed_nonneg P.flow c u y))
    have hlength := length_nonneg P.flow c u
    have hcap : m62TotalCurvature P.flow c u + m62Length P.flow c u ≤ E := by
      calc
        _ ≤ (m62TotalCurvature P.flow c a + m62Length P.flow c a) *
            Real.exp (Cbase * (u - a)) := hsum
        _ ≤ (Theta0 + L0) * Real.exp (Cbase * (u - a)) :=
          mul_le_mul_of_nonneg_right (add_le_add hTinitial hLinitial) (Real.exp_pos _).le
        _ ≤ (Theta0 + L0) * Real.exp (Cbase * max (b - a) 0) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left
              ((sub_le_sub_right hu.2 a).trans (le_max_left _ _)) hCbase))
            (add_nonneg hTheta0 hL0)
        _ = E := by dsimp only [E]; rw [add_comm Theta0 L0]
    constructor <;> linarith only [hcap, htheta, hlength]
  have htb : t ≤ b := ht.2.trans hEnd
  have hsclosed : s ∈ Icc a b := ⟨hs, ht.1.le.trans htb⟩
  have hstable := M63.c2_smallSubarcs_eventually P.flow hcompactP c hc hsclosed
    (show r / 2 < r by linarith only [hr]) hd0d hSmall
  have hlenNear : ∀ᶠ sigma in 𝓝[Icc a b] s, r / 2 < m62Length P.flow c sigma :=
    tendsto_const_nhds.eventually_lt (hest.length_continuous s hsclosed)
      (by linarith only [hLength, hr])
  have htimeNear : ∀ᶠ sigma in 𝓝[>] s, sigma < t :=
    (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
  have hdomainNear : ∀ᶠ sigma in 𝓝[>] s, sigma ∈ Icc a b := by
    filter_upwards [self_mem_nhdsWithin, htimeNear] with sigma hssigma hsigmat
    exact ⟨hs.trans hssigma.le, hsigmat.le.trans htb⟩
  have hto : Tendsto (fun sigma : Real => sigma) (𝓝[>] s) (𝓝[Icc a b] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, hdomainNear⟩
  have heventual : ∀ᶠ sigma in 𝓝[>] s,
      m62CurvatureSquared P.flow c t x ≤ 2 / (t - sigma) := by
    filter_upwards [self_mem_nhdsWithin, htimeNear,
      hstable.filter_mono hto, hlenNear.filter_mono hto] with sigma hssigma hsigmat hsm hlen
    have hasigma : a < sigma := hs.trans_lt hssigma
    have hfull : Icc sigma t ⊆ Icc a b := Icc_subset_Icc hasigma.le htb
    obtain ⟨phi, d, hphi, hbij, hpos, hshift, hdSmooth, _hspace, heq⟩ :=
      hlocal.fixed_relabeling b hab le_rfl (Icc a b) (Or.inl rfl) c hc sigma t
        hasigma hsigmat htb hfull
    let F' := m63RestrictClosedFlow P.flow sigma t hfull hsigmat
    have hd' : M62ShrinkingCurve F' d :=
      m63SmoothRestriction hdSmooth sigma t Subset.rfl hsigmat
    have hphi1 : ContDiff Real 1 phi := hphi.of_le (by norm_num)
    have hmono : StrictMono phi := strictMono_of_deriv_pos hpos
    have hlengthEq (u : Real) (hu : u ∈ Icc sigma t) :
        m62Length P.flow c u = m62Length F' d u :=
      M63.length_eq_of_relabeling F' hd' hphi1 hpos hshift hu (heq u hu)
    have htotalEq (u : Real) (hu : u ∈ Icc sigma t) :
        m62TotalCurvature P.flow c u = m62TotalCurvature F' d u :=
      M63.totalCurvature_eq_of_relabeling F' hd' hphi1 hpos hshift hu (heq u hu)
    have harcLength (u : Real) (hu : u ∈ Icc sigma t) (alpha beta : Real) :
        m63ArcLength P.flow c u alpha beta =
          m63ArcLength F' d u (phi alpha) (phi beta) := by
      have hequal := congrArg (fun gamma : Real → P.charts.Point =>
        m63ArcLength F' (fun y _ => gamma y) u alpha beta) (funext (heq u hu))
      have hv : Continuous (curveSpeed F' d u) :=
        (speed_continuousOn F' d hd').comp_continuous
          (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hu⟩)
      exact hequal.trans (M63.arcLength_comp F' d
        ((hd'.spatial_regular u hu).mdifferentiable (by norm_num)) hv hphi1 hpos alpha beta)
    have harcTurning (u : Real) (hu : u ∈ Icc sigma t) (alpha beta : Real) :
        m63ArcTotalCurvature P.flow c u alpha beta =
          m63ArcTotalCurvature F' d u (phi alpha) (phi beta) := by
      have hequal := congrArg (fun gamma : Real → P.charts.Point =>
        m63ArcTotalCurvature F' (fun y _ => gamma y) u alpha beta) (funext (heq u hu))
      exact hequal.trans (M63.smooth_arcTotalCurvature_comp F' d hd' hphi1 hpos hu alpha beta)
    have hsigma : sigma ∈ Icc sigma t := ⟨le_rfl, hsigmat.le⟩
    have hSmall' : M63SmallSubarcs F' d sigma (r / 2) delta := by
      intro alpha beta horder hperiod hlength
      obtain ⟨p, rfl⟩ := hbij.2 alpha
      obtain ⟨q, rfl⟩ := hbij.2 beta
      have hpq : p ≤ q := hmono.le_iff_le.mp horder
      have hper : q ≤ p + curvePeriod := hmono.le_iff_le.mp (by rwa [hshift])
      rw [← harcTurning sigma hsigma p q]
      apply hsm p q hpq hper
      rwa [harcLength sigma hsigma p q]
    have hLength' : r / 2 ≤ m62Length F' d sigma := by
      rw [← hlengthEq sigma hsigma]
      exact hlen.le
    have hGlobal' (u : Real) (hu : u ∈ Icc sigma t) :
        m62Length F' d u ≤ E ∧ m62TotalCurvature F' d u ≤ E := by
      rw [← hlengthEq u hu, ← htotalEq u hu]
      exact hglobal u (hfull hu)
    have hBounds' : CurveEvolutionAmbientBounds F' K K K :=
      ⟨fun u hu => hBounds.riemann u (hfull hu),
        fun u hu => hBounds.ricci_derivative u (hfull hu),
        fun u hu => hBounds.ricci u (hfull hu)⟩
    have hRiemann : ∀ u ∈ Icc sigma t, ∀ p : P.charts.Point,
        ∀ v : Fin 5 → TangentSpace (𝓡 (n + 1)) p,
        (∀ i, (F'.metric u).tangentNorm p (v i) ≤ 1) →
          |(F'.connection u).covariantTensorDerivative
            (F'.connection u).riemannEvaluation p v| ≤ K := by
      intro u hu p v hv
      exact ((hTensor circumference P 1 u (hfull hu) p).1 v hv).trans hKr1
    have hSecond : ∀ u ∈ Icc sigma t, ∀ p : P.charts.Point,
        ∀ v : Fin 4 → TangentSpace (𝓡 (n + 1)) p,
        (∀ i, (F'.metric u).tangentNorm p (v i) ≤ 1) →
          |(F'.connection u).covariantTensorDerivative
            ((F'.connection u).covariantTensorDerivative
              (F'.connection u).ricciEvaluation) p v| ≤ K := by
      intro u hu p v hv
      exact ((hTensor circumference P 2 u (hfull hu) p).2 v hv).trans hKr2
    have htime : t - sigma ≤ delta * (r / 2) ^ 2 := by
      calc
        _ ≤ t - s := sub_le_sub_left hssigma.le t
        _ ≤ delta0 * r ^ 2 := by linarith only [ht.2]
        _ ≤ 2 * (delta0 * r ^ 2) := le_mul_of_one_le_left
          (mul_nonneg hd0.le (sq_nonneg r)) (by norm_num)
        _ = delta * (r / 2) ^ 2 := by dsimp only [delta0]; ring
    have hbound := m63SmallSubarcs_curvature_bound F' d hd' hK hE hBounds'
      hRiemann hSecond hP1 hP2 psi (hpsi.of_le (by decide)) hRange hPlateau hSupport
      hFirst hSecondPsi le_rfl hsigmat le_rfl (half_pos hr)
      (by linarith only [hr1, hr]) hd hd1.le htime hLength' hGlobal' hSmall'
      hLoss.le hExp.le hTurn t ⟨hsigmat, le_rfl⟩ (phi x)
    have heqcurv : m62CurvatureSquared P.flow c t x =
        m62CurvatureSquared F' d t (phi x) :=
      M63.curvatureSquared_eq_of_relabeling F' hd'
        (hphi.differentiable (by norm_num)) hpos ⟨hsigmat.le, le_rfl⟩
        (heq t ⟨hsigmat.le, le_rfl⟩)
    exact heqcurv.le.trans hbound
  have hlimit : Tendsto (fun sigma : Real => 2 / (t - sigma)) (𝓝[>] s)
      (𝓝 (2 / (t - s))) :=
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (sub_pos.mpr ht.1).ne').tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlimit heventual

end PoincareConjecture
