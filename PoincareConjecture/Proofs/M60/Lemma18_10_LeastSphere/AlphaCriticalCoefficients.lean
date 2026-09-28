import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

noncomputable section

universe u

namespace PoincareConjecture.M60.SUWeakAlphaCoordinate

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
  {f : LoopPlane → EuclideanSpace ℝ (Fin n)}
  {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



theorem coefficient_bounds (S : SUWeakAlphaCoordinate g b alpha f V center R) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let u := f
    ∃ kappa C : ℝ, 0 < kappa ∧ 0 < C ∧
      ∀ z ∈ Metric.closedBall center R,
        ‖G (u z)‖ ≤ C ∧ ‖fderiv ℝ G (u z)‖ ≤ C ∧
          ∀ v, kappa * ‖v‖ ^ 2 ≤ G (u z) v v := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  let K := u '' Metric.closedBall center R
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    S.coordinate_continuous
  have hKt : K ⊆ (extChartAt (𝓡 n) b).target := by
    rintro y ⟨z, hz, rfl⟩
    exact S.coordinate_range hz
  obtain ⟨a, C, ha, hC, _, hb, hp⟩ := suAlpha_coordinate_metric_bounds g b hK hKt
  have hd : ContinuousOn (fderiv ℝ G) K :=
    ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
      (isOpen_extChartAt_target b) (by simp)).mono hKt
  obtain ⟨D, hD⟩ := hK.bddAbove_image (continuous_norm.comp_continuousOn hd)
  refine ⟨a, C + max D 0 + 1, ha, by positivity, fun z hz => ?_⟩
  have hzK : u z ∈ K := mem_image_of_mem _ hz
  refine ⟨(hb _ hzK).trans (by have := le_max_right D 0; linarith), ?_, hp _ hzK⟩
  exact (hD (mem_image_of_mem _ hzK)).trans (by
    have := le_max_left D 0
    linarith)

private theorem coefficient_memLp_top (S : SUWeakAlphaCoordinate g b alpha f V center R) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let u := f
    let mu := volume.restrict (Metric.ball center R)
    MemLp (fun z => G (u z)) ⊤ mu ∧ MemLp (fun z => fderiv ℝ G (u z)) ⊤ mu := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  have hmap : MapsTo u (Metric.closedBall center R)
      (extChartAt (𝓡 n) b).target := S.coordinate_range
  have hB := (g.contDiffOn_chartCoefficients b).continuousOn.comp
    S.coordinate_continuous hmap
  have hD := ((g.contDiffOn_chartCoefficients b).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target b) (by simp)).comp S.coordinate_continuous hmap
  obtain ⟨kappa, C, _, _, hb⟩ := S.coefficient_bounds
  refine ⟨memLp_top_of_bound
    ((hB.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C ?_,
    memLp_top_of_bound
    ((hD.mono Metric.ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (hb z (Metric.ball_subset_closedBall hz)).1
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (hb z (Metric.ball_subset_closedBall hz)).2.1


def flux (_S : SUWeakAlphaCoordinate g b alpha f V center R) (a : Fin n) (i : Fin 2)
    (z : LoopPlane) : ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  let Q := ∑ j : Fin 2, G (u z) (V j z) (V j z)
  2 * alpha * (1 + Q / suAlphaRoundFactor z) ^ (alpha - 1) *
    G (u z) (V i z) (EuclideanSpace.single a 1)


def sourceTerm (_S : SUWeakAlphaCoordinate g b alpha f V center R)
    (a : Fin n) (z : LoopPlane) : ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  let Q := ∑ j : Fin 2, G (u z) (V j z) (V j z);
  -(alpha * (1 + Q / suAlphaRoundFactor z) ^ (alpha - 1)) *
    ∑ i : Fin 2, fderiv ℝ G (u z) (EuclideanSpace.single a 1)
      (V i z) (V i z)

set_option maxHeartbeats 800000 in



theorem flux_source_memLp (S : SUWeakAlphaCoordinate g b alpha f V center R) (ha : 1 < alpha) :
    let mu := volume.restrict (Metric.ball center R)
    (∀ a i, MemLp (S.flux a i) (ENNReal.ofReal (2 * alpha / (2 * alpha - 1))) mu) ∧
      ∀ a, Integrable (S.sourceTerm a) mu := by
  let E := EuclideanSpace ℝ (Fin n)
  let G := g.pullbackCoefficients (chartAt E b).symm
  let u := f
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := ⟨by
    change volume.restrict (Metric.ball center R) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let pp := ENNReal.ofReal (2 * alpha)
  let aa := ENNReal.ofReal alpha
  let tt := ENNReal.ofReal alpha / ENNReal.ofReal (alpha - 1)
  let qq := ENNReal.ofReal (2 * alpha / (2 * alpha - 1))
  have ha0 : 0 < alpha := by linarith
  have hd : 0 < alpha - 1 := by linarith
  have hp0 : 0 < 2 * alpha := by positivity
  have hq0 : 0 < 2 * alpha - 1 := by linarith
  have ht : tt = ENNReal.ofReal (alpha / (alpha - 1)) :=
    (ENNReal.ofReal_div_of_pos hd).symm
  let : ENNReal.HolderTriple pp pp aa := ENNReal.HolderTriple.of_toReal (by
    simp only [pp, aa, ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_ofReal hp0.le]
    exact ⟨by field_simp; ring, hp0, hp0⟩)
  let : ENNReal.HolderTriple tt pp qq := ENNReal.HolderTriple.of_toReal (by
    simp only [ht, pp, qq, ENNReal.toReal_ofReal (le_of_lt (div_pos ha0 hd)),
      ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (le_of_lt (div_pos hp0 hq0))]
    exact ⟨by field_simp; ring, div_pos ha0 hd, hp0⟩)
  let : ENNReal.HolderConjugate tt aa := ENNReal.HolderTriple.of_toReal (by
    simp only [ht, aa, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (le_of_lt (div_pos ha0 hd)), ENNReal.toReal_ofReal ha0.le]
    exact ⟨by field_simp; ring, div_pos ha0 hd, ha0⟩)
  obtain ⟨hG, hDG⟩ := S.coefficient_memLp_top
  have hcol (i : Fin 2) : MemLp (V i) pp mu := S.column_memLp i
  have hGcol (i : Fin 2) : MemLp (fun z => G (u z) (V i z)) pp mu :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
      (p := pp) (q := ⊤) pp (hcol i) hG
  have hquad (i : Fin 2) :
      MemLp (fun z => G (u z) (V i z) (V i z)) aa mu := by
    have h := (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := pp) (q := pp) aa (hcol i) (hGcol i)
    exact h
  let Q (z : LoopPlane) := ∑ i : Fin 2, G (u z) (V i z) (V i z)
  have hQ : MemLp Q aa mu := memLp_finsetSum _ (fun i _ => hquad i)
  have hInv : MemLp (fun z => (suAlphaRoundFactor z)⁻¹) ⊤ mu := by
    have hc : Continuous (fun z : LoopPlane => (suAlphaRoundFactor z)⁻¹) := by
      have he : (fun z : LoopPlane => (suAlphaRoundFactor z)⁻¹) =
          fun z => (‖z‖ ^ 2 + 4) ^ 2 / 16 := by
        funext z
        simp [suAlphaRoundFactor]
      rw [he]
      fun_prop
    obtain ⟨C, hC⟩ := (isCompact_closedBall center R).bddAbove_image
      hc.norm.continuousOn
    exact memLp_top_of_bound hc.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact hC (mem_image_of_mem _ (Metric.ball_subset_closedBall hz)))
  let A (z : LoopPlane) := 1 + Q z / suAlphaRoundFactor z
  have hA : MemLp A aa mu := by
    simpa only [A, div_eq_mul_inv, Pi.add_def] using
      (memLp_const (1 : ℝ)).add (hInv.mul' hQ)
  obtain ⟨kappa, _, hk, _, hbounds⟩ := S.coefficient_bounds
  have hA0 : ∀ᵐ z ∂mu, 0 ≤ A z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hQ0 : 0 ≤ Q z := Finset.sum_nonneg fun i _ =>
      (mul_nonneg hk.le (sq_nonneg _)).trans
        ((hbounds z (Metric.ball_subset_closedBall hz)).2.2 (V i z))
    have hlam : 0 < suAlphaRoundFactor z := by dsimp [suAlphaRoundFactor]; positivity
    exact add_nonneg (by norm_num) (div_nonneg hQ0 hlam.le)
  let W (z : LoopPlane) := A z ^ (alpha - 1)
  have hW : MemLp W tt mu := by
    apply (hA.norm_rpow_div (ENNReal.ofReal (alpha - 1))).ae_eq
    filter_upwards [hA0] with z hz
    simp only [W, Real.norm_eq_abs, abs_of_nonneg hz, ENNReal.toReal_ofReal hd.le]
  constructor
  · intro a i
    change MemLp (fun z => S.flux a i z) qq mu
    have he : MemLp (fun z => EuclideanSpace.single a (1 : ℝ)) ⊤ mu := memLp_const _
    have hGi := (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := ⊤) (q := pp) pp he (hGcol i)
    have hprod : MemLp (fun z => 2 * alpha *
        (W z * G (u z) (V i z) (EuclideanSpace.single a 1))) qq mu :=
      (hGi.mul' hW).const_mul (2 * alpha)
    simpa only [flux, W, A, Q, G, u, mul_assoc] using hprod
  · intro a
    change Integrable (fun z => S.sourceTerm a z) mu
    have he : MemLp (fun z => EuclideanSpace.single a (1 : ℝ)) ⊤ mu := memLp_const _
    have hDGe : MemLp (fun z => fderiv ℝ G (u z) (EuclideanSpace.single a 1)) ⊤ mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := ⊤) (q := ⊤) ⊤ he hDG
    have hDGcol (i : Fin 2) : MemLp (fun z =>
        fderiv ℝ G (u z) (EuclideanSpace.single a 1) (V i z)) pp mu :=
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := pp) (q := ⊤) pp (hcol i) hDGe
    have hDQ (i : Fin 2) : MemLp (fun z =>
        fderiv ℝ G (u z) (EuclideanSpace.single a 1) (V i z) (V i z)) aa mu :=
      (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
        (p := pp) (q := pp) aa (hcol i) (hDGcol i)
    have hsum := memLp_finsetSum Finset.univ (fun i _ => hDQ i)
    have hprod := memLp_one_iff_integrable.mp ((hsum.mul' hW).const_mul (-alpha))
    simpa only [sourceTerm, W, A, Q, G, u, neg_mul, mul_assoc] using hprod

set_option maxHeartbeats 800000 in


theorem flux_source_memLp_one (S : SUWeakAlphaCoordinate g b 1 f V center R) :
    let mu := volume.restrict (Metric.ball center R)
    (∀ a i, MemLp (S.flux a i) 2 mu) ∧ ∀ a, Integrable (S.sourceTerm a) mu := by
  let E := EuclideanSpace ℝ (Fin n)
  let G := g.pullbackCoefficients (chartAt E b).symm
  let u := f
  let mu := volume.restrict (Metric.ball center R)
  obtain ⟨hG, hDG⟩ := S.coefficient_memLp_top
  have hcol (i : Fin 2) : MemLp (V i) 2 mu := by
    simpa only [mul_one, ENNReal.ofReal_ofNat] using S.column_memLp i
  have hGcol (i : Fin 2) : MemLp (fun z => G (u z) (V i z)) 2 mu :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (hcol i) hG
  constructor
  · intro a i
    change MemLp (fun z => S.flux a i z) 2 mu
    have he : MemLp (fun _ : LoopPlane => EuclideanSpace.single a (1 : ℝ)) ⊤ mu :=
      memLp_top_const _
    have hi := (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := ⊤) (q := 2) 2 he (hGcol i)
    simpa only [flux, sub_self, Real.rpow_zero, mul_one, G, u,
      ContinuousLinearMap.apply_apply] using hi.const_mul 2
  · intro a
    change Integrable (fun z => S.sourceTerm a z) mu
    have he : MemLp (fun _ : LoopPlane => EuclideanSpace.single a (1 : ℝ)) ⊤ mu :=
      memLp_top_const _
    have hDGe := (ContinuousLinearMap.apply ℝ (E →L[ℝ] E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
      (p := ⊤) (q := ⊤) ⊤ he hDG
    have hDQ (i : Fin 2) : MemLp (fun z =>
        fderiv ℝ G (u z) (EuclideanSpace.single a 1) (V i z) (V i z)) 1 mu := by
      have hDGi := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
        (p := 2) (q := ⊤) 2 (hcol i) hDGe
      have hi := (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
        (p := 2) (q := 2) 1 (hcol i) hDGi
      exact hi
    have hsum := (memLp_one_iff_integrable.mp
      (memLp_finsetSum Finset.univ (fun i _ => hDQ i))).neg
    simpa only [sourceTerm, sub_self, Real.rpow_zero, mul_one, neg_one_mul, G, u,
      Pi.neg_def] using hsum

private theorem component_variation (S : SUWeakAlphaCoordinate g b alpha f V center R)
    (a : Fin n) {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (z : LoopPlane) :
    suAlphaChartVariation g b alpha (f)
      V (fun x => phi x • EuclideanSpace.single a 1) z =
      (∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) -
        S.sourceTerm a z * phi z := by
  have hd := (hphi.differentiable (by simp) z).hasFDerivAt.smul_const
    (EuclideanSpace.single a (1 : ℝ))
  simp only [suAlphaChartVariation, flux, sourceTerm, hd.fderiv,
    ContinuousLinearMap.smulRight_apply, map_smul, smul_apply,
    smul_eq_mul]
  simp only [Fin.sum_univ_two]
  ring



theorem scalar_variation (S : SUWeakAlphaCoordinate g b alpha f V center R) (a : Fin n)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hO : tsupport phi ⊆ Metric.ball center R) :
    IntegrableOn (fun z =>
      (∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) -
        S.sourceTerm a z * phi z)
      (Metric.ball center R) ∧
    (∫ z in Metric.ball center R,
      (∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) -
        S.sourceTerm a z * phi z) = 0 := by
  let eta (z : LoopPlane) := phi z • EuclideanSpace.single a (1 : ℝ)
  have heta : ContDiff ℝ ∞ eta := hphi.smul contDiff_const
  have hetac : HasCompactSupport eta := hc.smul_right
  have hetaO : tsupport eta ⊆ Metric.ball center R :=
    (tsupport_smul_subset_left _ _).trans hO
  have heq : suAlphaChartVariation g b alpha
      (f) V eta = fun z =>
      (∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) -
        S.sourceTerm a z * phi z := funext (S.component_variation a hphi)
  exact ⟨heq ▸ S.variation_integrable eta heta hetac hetaO,
    heq ▸ S.variation_zero eta heta hetac hetaO⟩


theorem flux_source_memLp_of_one_le (S : SUWeakAlphaCoordinate g b alpha f V center R)
    (ha : 1 ≤ alpha) :
    let mu := volume.restrict (Metric.ball center R)
    (∀ a i, MemLp (S.flux a i) (ENNReal.ofReal (2 * alpha / (2 * alpha - 1))) mu) ∧
      ∀ a, Integrable (S.sourceTerm a) mu := by
  rcases ha.eq_or_lt with he | he
  · subst alpha
    simpa only [mul_one, sub_self, div_one, ENNReal.ofReal_ofNat, show (2 : ℝ) - 1 = 1 by
      norm_num] using S.flux_source_memLp_one
  · exact S.flux_source_memLp he



theorem scalar_equation (S : SUWeakAlphaCoordinate g b alpha f V center R) (ha : 1 ≤ alpha)
    (a : Fin n) {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi)
    (hO : tsupport phi ⊆ Metric.ball center R) :
    (∫ z in Metric.ball center R,
      ∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) =
      ∫ z in Metric.ball center R, S.sourceTerm a z * phi z := by
  let O := Metric.ball center R
  let mu := volume.restrict O
  obtain ⟨hF, hb⟩ := S.flux_source_memLp_of_one_le ha
  have hq : 1 ≤ ENNReal.ofReal (2 * alpha / (2 * alpha - 1)) := by
    have hreal : (1 : ℝ) ≤ 2 * alpha / (2 * alpha - 1) := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
  have hleft : Integrable (fun z =>
      ∑ i : Fin 2, S.flux a i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) mu := by
    apply integrable_finsetSum
    intro i _
    have hi := ((hF a i).locallyIntegrable hq).integrable_smul_right_of_hasCompactSupport
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ)))
    simpa only [smul_eq_mul] using hi
  have hright : Integrable (fun z => S.sourceTerm a z * phi z) mu := by
    have hi := (hb a).locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      hphi.continuous hc
    simpa only [smul_eq_mul] using hi
  have heq := (S.scalar_variation a hphi hc hO).2
  rw [integral_sub hleft hright, sub_eq_zero] at heq
  exact heq


def naturalWeight (_S : SUWeakAlphaCoordinate g b alpha f V center R) (z : LoopPlane) : ℝ :=
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  (1 + (∑ i : Fin 2, G (u z) (V i z) (V i z)) /
    suAlphaRoundFactor z) ^ (alpha - 1)

private theorem sum_components_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : EuclideanSpace ℝ (Fin n)) :
    (∑ a : Fin n, v a • L (EuclideanSpace.single a 1)) = L v := by
  have hv : (∑ a : Fin n, v a • EuclideanSpace.single a (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  rw [← hv]
  simp only [map_sum, map_smul]
  rw [hv]

theorem flux_pairing (S : SUWeakAlphaCoordinate g b alpha f V center R) (z : LoopPlane)
    (i : Fin 2) (v : EuclideanSpace ℝ (Fin n)) :
    (∑ a : Fin n, S.flux a i z * v a) = 2 * alpha * S.naturalWeight z *
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
        (f z) (V i z) v := by
  let L := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    (f z) (V i z)
  have hs : (∑ a : Fin n, L (EuclideanSpace.single a 1) * v a) = L v := by
    simpa only [smul_eq_mul, mul_comm] using sum_components_smul L v
  change (∑ a : Fin n, (2 * alpha * S.naturalWeight z *
    L (EuclideanSpace.single a 1)) * v a) = 2 * alpha * S.naturalWeight z * L v
  simpa only [Finset.mul_sum, mul_assoc] using
    congrArg (fun t : ℝ => 2 * alpha * S.naturalWeight z * t) hs

theorem source_pairing (S : SUWeakAlphaCoordinate g b alpha f V center R) (z : LoopPlane)
    (v : EuclideanSpace ℝ (Fin n)) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let u := f
    (∑ a : Fin n, S.sourceTerm a z * v a) = -(alpha * S.naturalWeight z) *
      ∑ i : Fin 2, fderiv ℝ G (u z) v (V i z) (V i z) := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  have hi (i : Fin 2) :
      (∑ a : Fin n, fderiv ℝ G (u z) (EuclideanSpace.single a 1)
        (V i z) (V i z) * v a) =
          fderiv ℝ G (u z) v (V i z) (V i z) := by
    have h := congrArg
      (fun B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        B (V i z) (V i z)) (sum_components_smul (fderiv ℝ G (u z)) v)
    simpa only [sum_apply, smul_apply, smul_eq_mul, mul_comm] using h
  change (∑ a : Fin n, (-(alpha * S.naturalWeight z) *
    ∑ i : Fin 2, fderiv ℝ G (u z) (EuclideanSpace.single a 1)
      (V i z) (V i z)) * v a) = _
  simp only [mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hi]
  rfl



theorem natural_coercivity_source (S : SUWeakAlphaCoordinate g b alpha f V center R)
    (ha : 1 ≤ alpha) :
    ∃ kappa C : ℝ, 0 < kappa ∧ 0 < C ∧
      ∀ z ∈ Metric.closedBall center R,
        1 ≤ S.naturalWeight z ∧
        (2 * alpha * kappa * S.naturalWeight z * ∑ i : Fin 2, ‖V i z‖ ^ 2 ≤
          ∑ a : Fin n, ∑ i : Fin 2, S.flux a i z * V i z a) ∧
        ∀ v : EuclideanSpace ℝ (Fin n),
          |∑ a : Fin n, S.sourceTerm a z * v a| ≤
            alpha * C * ‖v‖ * S.naturalWeight z * ∑ i : Fin 2, ‖V i z‖ ^ 2 := by
  obtain ⟨kappa, C, hk, hC, hb⟩ := S.coefficient_bounds
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  refine ⟨kappa, C, hk, hC, fun z hz => ?_⟩
  have hQ : 0 ≤ ∑ i : Fin 2, G (u z) (V i z) (V i z) :=
    Finset.sum_nonneg fun i _ => (mul_nonneg hk.le (sq_nonneg _)).trans ((hb z hz).2.2 _)
  have hw : 1 ≤ S.naturalWeight z := by
    change 1 ≤ (1 + (∑ i : Fin 2, G (u z) (V i z) (V i z)) /
      suAlphaRoundFactor z) ^ (alpha - 1)
    apply Real.one_le_rpow
    · have hlam : 0 < suAlphaRoundFactor z := by dsimp [suAlphaRoundFactor]; positivity
      linarith [div_nonneg hQ hlam.le]
    · linarith
  have hw0 := zero_le_one.trans hw
  refine ⟨hw, ?_, fun v => ?_⟩
  · rw [Finset.sum_comm]
    simp_rw [S.flux_pairing]
    rw [← Finset.mul_sum]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) =>
      (hb z hz).2.2 (V i z))
    rw [← Finset.mul_sum] at hsum
    calc
      _ = (2 * alpha * S.naturalWeight z) *
          (kappa * ∑ i : Fin 2, ‖V i z‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  · rw [S.source_pairing]
    have hD (i : Fin 2) :
        |fderiv ℝ G (u z) v (V i z) (V i z)| ≤
          C * ‖v‖ * ‖V i z‖ ^ 2 := by
      calc
        _ = ‖fderiv ℝ G (u z) v (V i z) (V i z)‖ := rfl
        _ ≤ ‖fderiv ℝ G (u z) v (V i z)‖ * ‖V i z‖ :=
          (fderiv ℝ G (u z) v (V i z)).le_opNorm _
        _ ≤ (‖fderiv ℝ G (u z) v‖ * ‖V i z‖) * ‖V i z‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ G (u z) v).le_opNorm _) (norm_nonneg _)
        _ ≤ ((‖fderiv ℝ G (u z)‖ * ‖v‖) * ‖V i z‖) * ‖V i z‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ((fderiv ℝ G (u z)).le_opNorm _) (norm_nonneg _))
            (norm_nonneg _)
        _ ≤ ((C * ‖v‖) * ‖V i z‖) * ‖V i z‖ := by
          gcongr
          exact (hb z hz).2.1
        _ = _ := by ring
    have hsum := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
      (Finset.sum_le_sum (fun i _ => hD i))
    rw [← Finset.mul_sum] at hsum
    rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) hw0)]
    exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by linarith) hw0)).trans_eq (by ring)



theorem natural_cross_bound (S : SUWeakAlphaCoordinate g b alpha f V center R) (z : LoopPlane)
    {C : ℝ}
    (hG : ‖g.pullbackCoefficients
      (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
        (f z)‖ ≤ C)
    (v : EuclideanSpace ℝ (Fin n)) (d : Fin 2 → ℝ) :
    (∑ a : Fin n, ∑ i : Fin 2, S.flux a i z * v a * d i) ^ 2 ≤
      (2 * alpha * C) ^ 2 * ‖v‖ ^ 2 * S.naturalWeight z ^ 2 *
        (∑ i : Fin 2, ‖V i z‖ ^ 2) * ∑ i : Fin 2, d i ^ 2 := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    (f z)
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have habs (i : Fin 2) : |G (V i z) v| ≤ C * ‖V i z‖ * ‖v‖ := by
    calc
      _ = ‖G (V i z) v‖ := rfl
      _ ≤ ‖G (V i z)‖ * ‖v‖ := (G (V i z)).le_opNorm v
      _ ≤ (‖G‖ * ‖V i z‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (G.le_opNorm _) (norm_nonneg _)
      _ ≤ _ := by gcongr
  have hsq (i : Fin 2) : (G (V i z) v) ^ 2 ≤
      C ^ 2 * ‖v‖ ^ 2 * ‖V i z‖ ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (habs i)
    simpa only [sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hsq i)
  rw [← Finset.mul_sum] at hsum
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => G (V i z) v) d
  have hd0 : 0 ≤ ∑ i : Fin 2, d i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_right hsum hd0)
  have heq : (∑ a : Fin n, ∑ i : Fin 2, S.flux a i z * v a * d i) =
      2 * alpha * S.naturalWeight z * ∑ i : Fin 2, G (V i z) v * d i := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, S.flux_pairing]
    simp only [G, Finset.mul_sum, mul_assoc]
  rw [heq, mul_pow]
  exact (mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)).trans_eq (by ring)

set_option maxHeartbeats 800000 in



theorem natural_integrability (S : SUWeakAlphaCoordinate g b alpha f V center R) (ha : 1 ≤ alpha) :
    let mu := volume.restrict (Metric.ball center R)
    MemLp S.naturalWeight (ENNReal.ofReal alpha / ENNReal.ofReal (alpha - 1)) mu ∧
      Integrable (fun z => S.naturalWeight z * ∑ i : Fin 2, ‖V i z‖ ^ 2) mu := by
  let E := EuclideanSpace ℝ (Fin n)
  let G := g.pullbackCoefficients (chartAt E b).symm
  let u := f
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := ⟨by
    change volume.restrict (Metric.ball center R) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let pp := ENNReal.ofReal (2 * alpha)
  let aa := ENNReal.ofReal alpha
  let tt := aa / ENNReal.ofReal (alpha - 1)
  have ha0 : 0 < alpha := by linarith
  have hp0 : 0 < 2 * alpha := by positivity
  let : ENNReal.HolderTriple pp pp aa := ENNReal.HolderTriple.of_toReal (by
    simp only [pp, aa, ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_ofReal hp0.le]
    exact ⟨by field_simp; ring, hp0, hp0⟩)
  let : ENNReal.HolderConjugate tt aa := by
    by_cases he : alpha = 1
    · subst alpha
      simp only [tt, aa, sub_self, ENNReal.ofReal_zero, ENNReal.ofReal_one,
        ENNReal.div_zero, ne_eq, one_ne_zero, not_false_eq_true]
      infer_instance
    · have hd : 0 < alpha - 1 := sub_pos.mpr (lt_of_le_of_ne ha (Ne.symm he))
      have ht : tt = ENNReal.ofReal (alpha / (alpha - 1)) :=
        (ENNReal.ofReal_div_of_pos hd).symm
      apply ENNReal.HolderTriple.of_toReal
      simp only [ht, aa, ENNReal.toReal_one,
        ENNReal.toReal_ofReal (le_of_lt (div_pos ha0 hd)), ENNReal.toReal_ofReal ha0.le]
      exact ⟨by field_simp; ring, div_pos ha0 hd, ha0⟩
  obtain ⟨hG, _⟩ := S.coefficient_memLp_top
  have hcol (i : Fin 2) : MemLp (V i) pp mu := S.column_memLp i
  have hquad (i : Fin 2) : MemLp (fun z => G (u z) (V i z) (V i z)) aa mu := by
    have hGcol := (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (E := E)).memLp_of_bilin
      (p := pp) (q := ⊤) pp (hcol i) hG
    have hi := (ContinuousLinearMap.apply ℝ ℝ (E := E)).memLp_of_bilin
      (p := pp) (q := pp) aa (hcol i) hGcol
    exact hi
  let Q (z : LoopPlane) := ∑ i : Fin 2, G (u z) (V i z) (V i z)
  have hQ : MemLp Q aa mu := memLp_finsetSum _ (fun i _ => hquad i)
  have hInv : MemLp (fun z => (suAlphaRoundFactor z)⁻¹) ⊤ mu := by
    have hc : Continuous (fun z : LoopPlane => (suAlphaRoundFactor z)⁻¹) := by
      have he : (fun z : LoopPlane => (suAlphaRoundFactor z)⁻¹) =
          fun z => (‖z‖ ^ 2 + 4) ^ 2 / 16 := by
        funext z
        simp [suAlphaRoundFactor]
      rw [he]
      fun_prop
    obtain ⟨C, hC⟩ := (isCompact_closedBall center R).bddAbove_image
      hc.norm.continuousOn
    exact memLp_top_of_bound hc.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact hC (mem_image_of_mem _ (Metric.ball_subset_closedBall hz)))
  let A (z : LoopPlane) := 1 + Q z / suAlphaRoundFactor z
  have hA : MemLp A aa mu := by
    simpa only [A, div_eq_mul_inv, Pi.add_def] using
      (memLp_const (1 : ℝ)).add (hInv.mul' hQ)
  obtain ⟨kappa, _, hk, _, hbounds⟩ := S.coefficient_bounds
  have hA0 : ∀ᵐ z ∂mu, 0 ≤ A z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hQ0 : 0 ≤ Q z := Finset.sum_nonneg fun i _ =>
      (mul_nonneg hk.le (sq_nonneg _)).trans
        ((hbounds z (Metric.ball_subset_closedBall hz)).2.2 (V i z))
    have hlam : 0 < suAlphaRoundFactor z := by dsimp [suAlphaRoundFactor]; positivity
    exact add_nonneg (by norm_num) (div_nonneg hQ0 hlam.le)
  have hW : MemLp S.naturalWeight tt mu := by
    apply (hA.norm_rpow_div (ENNReal.ofReal (alpha - 1))).ae_eq
    filter_upwards [hA0] with z hz
    simp only [naturalWeight, A, Q, G, u, Real.norm_eq_abs, abs_of_nonneg hz,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ha)]
  refine ⟨hW, ?_⟩
  have hnormsq (i : Fin 2) : MemLp (fun z => ‖V i z‖ ^ 2) aa mu := by
    simpa only [pow_two] using (hcol i).norm.mul' (hcol i).norm
  exact memLp_one_iff_integrable.mp ((memLp_finsetSum _ (fun i _ => hnormsq i)).mul' hW)




theorem coefficient_neighborhood (S : SUWeakAlphaCoordinate g b alpha f V center R) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let u := f
    let z0 := center
    ∃ r kappa C : ℝ, 0 < r ∧ 0 < kappa ∧ 0 < C ∧
      Metric.closedBall (u z0) r ⊆ (extChartAt (𝓡 n) b).target ∧
      (∀ y ∈ Metric.closedBall (u z0) r,
        ‖G y‖ ≤ C ∧ ‖fderiv ℝ G y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ G) y‖ ≤ C ∧
          ∀ v, kappa * ‖v‖ ^ 2 ≤ G y v v) ∧
      ∀ delta : ℝ, 0 < delta → ∃ innerRadius : ℝ, 0 < innerRadius ∧ innerRadius < R ∧
        MapsTo u (Metric.closedBall z0 innerRadius)
          (Metric.ball (u z0) (min delta (r / 2))) := by
  let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let u := f
  let z0 := center
  have hz0 : z0 ∈ Metric.closedBall z0 R := Metric.mem_closedBall_self S.radius_pos.le
  have hy0 : u z0 ∈ (extChartAt (𝓡 n) b).target := S.coordinate_range hz0
  obtain ⟨r0, hr0, hrange⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target b).mem_nhds hy0)
  let K := Metric.closedBall (u z0) (r0 / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ (extChartAt (𝓡 n) b).target :=
    (Metric.closedBall_subset_ball (by linarith : r0 / 2 < r0)).trans hrange
  obtain ⟨kappa, C0, hk, hC0, _, hG, hpos⟩ :=
    suAlpha_coordinate_metric_bounds g b hK hKt
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ G) (extChartAt (𝓡 n) b).target :=
    (g.contDiffOn_chartCoefficients b).fderiv_of_isOpen
      (isOpen_extChartAt_target b) (by simp)
  have hD2G : ContinuousOn (fderiv ℝ (fderiv ℝ G)) K :=
    (hDG.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target b) (by simp)).mono hKt
  obtain ⟨C1, hC1⟩ := hK.bddAbove_image (continuous_norm.comp_continuousOn
    (hDG.continuousOn.mono hKt))
  obtain ⟨C2, hC2⟩ := hK.bddAbove_image (continuous_norm.comp_continuousOn hD2G)
  refine ⟨r0 / 2, kappa, C0 + max C1 0 + max C2 0 + 1, by positivity, hk,
    by positivity, hKt, ?_, ?_⟩
  · intro y hy
    have h1 := hC1 (mem_image_of_mem _ hy)
    have h2 := hC2 (mem_image_of_mem _ hy)
    dsimp only [Function.comp_apply, G] at h1 h2
    have hm10 := le_max_right C1 0
    have hm20 := le_max_right C2 0
    have hm1 := le_max_left C1 0
    have hm2 := le_max_left C2 0
    exact ⟨(hG y hy).trans (by linarith), by linarith, by linarith, hpos y hy⟩
  · intro delta hdelta
    have huc : ContinuousAt u z0 := S.coordinate_continuous.continuousAt
      (Metric.closedBall_mem_nhds z0 S.radius_pos)
    have heps : 0 < min delta (r0 / 2 / 2) := lt_min hdelta (by positivity)
    obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp
      (huc.preimage_mem_nhds (Metric.ball_mem_nhds (u z0) heps))
    refine ⟨min (s / 2) (R / 2), lt_min (half_pos hs) (half_pos S.radius_pos),
      (min_le_right _ _).trans_lt (by linarith [S.radius_pos]), ?_⟩
    exact fun x hx => hball ((Metric.closedBall_subset_ball
      ((min_le_left _ _).trans_lt (by linarith : s / 2 < s))) hx)




theorem canonical_integrability (S : SUWeakAlphaCoordinate g b alpha f V center R)
    (ha : 1 ≤ alpha) :
    let mu := volume.restrict (Metric.ball center R)
    let Q := fun z => 1 + ‖(V 0 z, V 1 z)‖ ^ 2
    MemLp (fun z => Q z ^ (alpha - 1))
        (ENNReal.ofReal alpha / ENNReal.ofReal (alpha - 1)) mu ∧
      Integrable (fun z => Q z ^ alpha) mu := by
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let pp := ENNReal.ofReal (2 * alpha)
  let aa := ENNReal.ofReal alpha
  let q := fun z => (V 0 z, V 1 z)
  let Q := fun z => 1 + ‖q z‖ ^ 2
  have ha0 : 0 < alpha := by linarith
  have hp0 : 0 < 2 * alpha := by positivity
  let : ENNReal.HolderTriple pp pp aa := ENNReal.HolderTriple.of_toReal (by
    simp only [pp, aa, ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_ofReal hp0.le]
    exact ⟨by field_simp; ring, hp0, hp0⟩)
  have hq : MemLp q pp mu := memLp_prod_iff.mpr ⟨S.column_memLp 0, S.column_memLp 1⟩
  have hsq : MemLp (fun z => ‖q z‖ ^ 2) aa mu := by
    simpa only [pow_two] using hq.norm.mul' hq.norm
  have hQ : MemLp Q aa mu := (memLp_const (1 : ℝ)).add hsq
  have hW := (hQ.norm_rpow_div (ENNReal.ofReal (alpha - 1))).ae_eq
    (MeasureTheory.ae_of_all mu fun z => show ‖Q z‖ ^ (ENNReal.ofReal (alpha - 1)).toReal =
        Q z ^ (alpha - 1) by
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr ha), Real.norm_eq_abs,
        abs_of_nonneg (by dsimp [Q]; positivity)])
  have hH := hQ.norm_rpow_div aa
  have haa : aa / aa = 1 := ENNReal.div_self
    (ENNReal.ofReal_pos.mpr ha0).ne' ENNReal.ofReal_ne_top
  rw [haa] at hH
  refine ⟨hW, memLp_one_iff_integrable.mp (hH.ae_eq ?_)⟩
  exact MeasureTheory.ae_of_all mu fun z => by
    simp only [aa, ENNReal.toReal_ofReal ha0.le, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ Q z by dsimp [Q]; positivity)]
    rfl



theorem indicator_equation (S : SUWeakAlphaCoordinate g b alpha f V center R) (ha : 1 ≤ alpha)
    {r : ℝ} (hrR : r ≤ R) (a : Fin n)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center r) :
    (∫ x, ∑ i : Fin 2, (Metric.ball center r).indicator (S.flux a i) x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x, (Metric.ball center r).indicator (S.sourceTerm a) x * phi x := by
  classical
  have hsub := Metric.ball_subset_ball (x := center) hrR
  have heq := S.scalar_equation ha a hphi hc (hs.trans hsub)
  have hD (x : LoopPlane) (hx : x ∉ Metric.ball center r) (i : Fin 2) :
      fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
      (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
  have hp (x : LoopPlane) (hx : x ∉ Metric.ball center r) : phi x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by simp only [hD x hx.2, mul_zero, Finset.sum_const_zero]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by rw [hp x hx.2, mul_zero])] at heq
  have hleft : (fun x => ∑ i : Fin 2,
      (Metric.ball center r).indicator (S.flux a i) x *
        fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      (Metric.ball center r).indicator (fun x => ∑ i : Fin 2,
        S.flux a i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ Metric.ball center r <;> simp [hx]
  have hright : (fun x => (Metric.ball center r).indicator (S.sourceTerm a) x * phi x) =
      (Metric.ball center r).indicator (fun x => S.sourceTerm a x * phi x) := by
    funext x
    by_cases hx : x ∈ Metric.ball center r <;> simp [hx]
  rw [hleft, hright, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball]
  exact heq

end PoincareConjecture.M60.SUWeakAlphaCoordinate
