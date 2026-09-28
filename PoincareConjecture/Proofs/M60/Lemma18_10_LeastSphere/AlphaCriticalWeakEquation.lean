import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalFluxChain
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetWeakCalculus










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff ENNReal Manifold

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak



def suAlphaJetEquiv {n : ℕ} : EuclideanSpace ℝ (Fin ((2 + n) + (n + n))) ≃L[ℝ]
    ((LoopPlane × EuclideanSpace ℝ (Fin n)) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
  EuclideanSpace.finAddEquivProd.trans
    (EuclideanSpace.finAddEquivProd.prodCongr EuclideanSpace.finAddEquivProd)



def suWeakAlphaJet {n : ℕ} (u : LoopPlane → EuclideanSpace ℝ (Fin n))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (x : LoopPlane) : EuclideanSpace ℝ (Fin ((2 + n) + (n + n))) :=
  suAlphaJetEquiv.symm ((x, u x), (V 0 x, V 1 x))



def suWeakAlphaJetColumn {n : ℕ}
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (H : Fin 2 → Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
    (i : Fin 2) (x : LoopPlane) : EuclideanSpace ℝ (Fin ((2 + n) + (n + n))) :=
  suAlphaJetEquiv.symm ((EuclideanSpace.single i 1, V i x), (H 0 i x, H 1 i x))




theorem SUInitialGain.weak_jet_data {n : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {a : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V a R) :
    MemLp (suWeakAlphaJet u V) 4 (volume.restrict (Metric.ball a G.radius)) ∧
      (∀ i, MemLp (suWeakAlphaJetColumn V G.hessian i) 2
        (volume.restrict (Metric.ball a G.radius))) ∧
      ∀ i b, HasWeakPartialDeriv i (fun x => suWeakAlphaJetColumn V G.hessian i x b)
        (fun x => suWeakAlphaJet u V x b) (Metric.ball a G.radius) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a G.radius)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a G.radius) < ⊤)⟩
  have hV4 (i : Fin 2) : MemLp (V i) 4 (volume.restrict (Metric.ball a G.radius)) := by
    simpa using G.column_memLp 4 (by norm_num) i
  have hV2 (i : Fin 2) : MemLp (V i) 2 (volume.restrict (Metric.ball a G.radius)) := by
    simpa using G.column_memLp 2 (by norm_num) i
  refine ⟨?_, ?_, ?_⟩
  · exact suAlphaJetEquiv.symm.toContinuousLinearMap.comp_memLp'
      (memLp_prod_iff.mpr ⟨memLp_prod_iff.mpr
        ⟨suContinuous_memLp_ball continuousOn_id, suContinuous_memLp_ball G.coordinate_continuous⟩,
        memLp_prod_iff.mpr ⟨hV4 0, hV4 1⟩⟩)
  · intro i
    exact suAlphaJetEquiv.symm.toContinuousLinearMap.comp_memLp'
      (memLp_prod_iff.mpr ⟨memLp_prod_iff.mpr ⟨memLp_const _, hV2 i⟩,
        memLp_prod_iff.mpr ⟨G.hessian_memLp 0 i, G.hessian_memLp 1 i⟩⟩)
  · intro i b
    have he (x : LoopPlane) : suWeakAlphaJet u V x =
        EuclideanSpace.finAddEquivProd.symm
          (EuclideanSpace.finAddEquivProd.symm (x, u x),
            EuclideanSpace.finAddEquivProd.symm (V 0 x, V 1 x)) := rfl
    have heW (x : LoopPlane) : suWeakAlphaJetColumn V G.hessian i x =
        EuclideanSpace.finAddEquivProd.symm
          (EuclideanSpace.finAddEquivProd.symm (EuclideanSpace.single i 1, V i x),
            EuclideanSpace.finAddEquivProd.symm (G.hessian 0 i x, G.hessian 1 i x)) := rfl
    cases b using Fin.addCases with
    | left k =>
      simp only [he, heW, suFinAddEquivProd_symm_left]
      cases k using Fin.addCases with
      | left j =>
        simp only [suFinAddEquivProd_symm_left]
        have ht := HasWeakPartialDeriv.of_contDiff (i := i)
          (Ω := Metric.ball a G.radius) Metric.isOpen_ball
          ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff : ContDiff ℝ 1 _)
        simpa only [HasWeakPartialDeriv, ContinuousLinearMap.fderiv, PiLp.proj_apply] using ht
      | right j =>
        simpa only [suFinAddEquivProd_symm_right] using G.weak_derivative i j
    | right k =>
      simp only [he, heW, suFinAddEquivProd_symm_right]
      cases k using Fin.addCases with
      | left j =>
        simpa only [suFinAddEquivProd_symm_left] using G.second_weak_derivative 0 i j
      | right j =>
        simpa only [suFinAddEquivProd_symm_right] using G.second_weak_derivative 1 i j

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace




theorem suAlphaJetFlux_extension
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : alpha ≤ 3 / 2)
    {K : Set (LoopPlane × EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : ∀ x ∈ K, x.2 ∈ (extChartAt (𝓡 n) b).target)
    (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    ∃ (F : EuclideanSpace ℝ (Fin ((2 + n) + (n + n))) → ℝ) (C : ℝ),
      ContDiff ℝ 1 F ∧ 0 < C ∧
      (∀ z, ‖fderiv ℝ F z‖ ≤ C * (1 + ‖z‖ ^ 2)) ∧
      ∀ x ∈ K, ∀ q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        F =ᶠ[𝓝 (suAlphaJetEquiv.symm (x, q))] fun z =>
          suAlphaCoordinateFlux g b alpha (suAlphaJetEquiv z).1 (suAlphaJetEquiv z).2 w := by
  let E := EuclideanSpace ℝ (Fin n)
  let P := EuclideanSpace ℝ (Fin (2 + n))
  let Q := EuclideanSpace ℝ (Fin (n + n))
  let ep : P ≃L[ℝ] LoopPlane × E := EuclideanSpace.finAddEquivProd
  let eq : Q ≃L[ℝ] E × E := EuclideanSpace.finAddEquivProd
  let ee : EuclideanSpace ℝ (Fin ((2 + n) + (n + n))) ≃L[ℝ] P × Q :=
    EuclideanSpace.finAddEquivProd
  let metric := g.pullbackCoefficients (chartAt E b).symm
  let O : Set P := ep ⁻¹' (univ ×ˢ (extChartAt (𝓡 n) b).target)
  let B : P → Q →L[ℝ] Q →L[ℝ] ℝ := fun z =>
    ((suAlphaRoundFactor (ep z).1)⁻¹ • suAlphaPairMetric (metric (ep z).2)).bilinearComp
      eq.toContinuousLinearMap eq.toContinuousLinearMap
  let l : P → ℝ := fun z => suAlphaRoundFactor (ep z).1
  have hO : IsOpen O := (isOpen_univ.prod (isOpen_extChartAt_target b)).preimage ep.continuous
  have hlpos (z : P) : 0 < l z := by dsimp [l, suAlphaRoundFactor]; positivity
  have hl : ContDiff ℝ 1 l := by
    have hround : ContDiff ℝ 1 suAlphaRoundFactor := by
      unfold suAlphaRoundFactor
      exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
        (fun z => by positivity)
    exact hround.comp (contDiff_fst.comp ep.contDiff)
  have hmetric : ContDiffOn ℝ 1 (fun z : P => metric (ep z).2) O :=
    (g.contDiffOn_chartCoefficients b).of_le (by simp) |>.comp
      (contDiff_snd.comp ep.contDiff).contDiffOn (fun _ hz => hz.2)
  have hB : ContDiffOn ℝ 1 B O := by
    apply contDiffOn_clm_apply.mpr
    intro q
    apply contDiffOn_clm_apply.mpr
    intro r
    change ContDiffOn ℝ 1 (fun z => (l z)⁻¹ *
      (metric (ep z).2 (eq q).1 (eq r).1 + metric (ep z).2 (eq q).2 (eq r).2)) O
    exact (hl.inv (fun z => (hlpos z).ne')).contDiffOn.mul
      (((hmetric.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
        ((hmetric.clm_apply contDiffOn_const).clm_apply contDiffOn_const))
  have hBpos (z : P) (hz : z ∈ O) (q : Q) (hq : q ≠ 0) : 0 < B z q q := by
    obtain ⟨k, _, hk, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
      (isCompact_singleton (x := (ep z).2)) (singleton_subset_iff.mpr hz.2)
    have hp := suAlphaPairMetric_coercive (metric (ep z).2) hk.le
      (hmetric _ (mem_singleton _)) (eq q)
    have hq' : eq q ≠ 0 := fun he => hq (eq.injective (by simpa using he))
    have hpos : 0 < suAlphaPairMetric (metric (ep z).2) (eq q) (eq q) :=
      (mul_pos hk (sq_pos_of_pos (norm_pos_iff.mpr hq'))).trans_le hp
    exact mul_pos (inv_pos.mpr (hlpos z)) hpos
  obtain ⟨A, C, hA, hC, hDA, he⟩ := suAlphaFlux_supported_extension hO
    (hK.image ep.symm.continuous) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, by simpa only [ep.apply_symm_apply] using hKt x hx⟩)
    B (fun _ => 1) l ha hB contDiffOn_const hl.contDiffOn
    (fun _ _ => zero_lt_one) hBpos
  let L : (Q →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (eq.symm w)
  let F := L ∘ A ∘ ee
  obtain ⟨D, hD, hDb⟩ := suQuadraticDerivative_comp_linear hA hC hDA ee.toContinuousLinearMap
  have hAe : ContDiff ℝ 1 (A ∘ ee) := hA.comp ee.contDiff
  refine ⟨F, D * (‖L‖ + 1), L.contDiff.comp hAe, by positivity, ?_, ?_⟩
  · intro z
    change ‖fderiv ℝ (L ∘ (A ∘ ee)) z‖ ≤ _
    rw [fderiv_comp z L.differentiableAt (hAe.differentiable (by norm_num) z), L.fderiv]
    calc
      _ ≤ ‖L‖ * ‖fderiv ℝ (A ∘ ee) z‖ := opNorm_comp_le _ _
      _ ≤ ‖L‖ * (D * (1 + ‖z‖ ^ 2)) := mul_le_mul_of_nonneg_left (hDb z) (norm_nonneg L)
      _ ≤ _ := by nlinarith [mul_nonneg hD.le (sq_nonneg ‖z‖)]
  · intro x hx q
    have hpoint : ee (suAlphaJetEquiv.symm (x, q)) = (ep.symm x, eq.symm q) :=
      ee.apply_symm_apply _
    have ht : Tendsto ee (𝓝 (suAlphaJetEquiv.symm (x, q))) (𝓝 (ep.symm x, eq.symm q)) := by
      simpa only [hpoint] using
        (ee.continuous.continuousAt.tendsto (x := suAlphaJetEquiv.symm (x, q)))
    have hc := (he (ep.symm x) (mem_image_of_mem _ hx) (eq.symm q)).comp_tendsto
      ht
    filter_upwards [hc] with z hz
    simp only [Function.comp_apply] at hz
    change L (A (ee z)) = _
    rw [hz]
    change l (ee z).1 * (2 * alpha *
      (1 + B (ee z).1 (ee z).2 (ee z).2) ^ (alpha - 1) *
        B (ee z).1 (ee z).2 (eq.symm w)) = _
    simp only [B, bilinearComp_apply]
    have hw : eq.toContinuousLinearMap (eq.symm w) = w := eq.apply_symm_apply w
    rw [hw]
    rfl




def suAlphaJetFlux
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (a : Fin n) (i : Fin 2)
    (z : EuclideanSpace ℝ (Fin ((2 + n) + (n + n)))) : ℝ :=
  suAlphaCoordinateFlux g b alpha (suAlphaJetEquiv z).1 (suAlphaJetEquiv z).2
    (if i = 0 then (EuclideanSpace.single a 1, 0) else (0, EuclideanSpace.single a 1))



theorem SUWeakAlphaCoordinate.jet_flux_eq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (a : Fin n) (i : Fin 2) (x : LoopPlane) :
    suAlphaJetFlux g b alpha a i (suWeakAlphaJet u V x) = S.flux a i x := by
  unfold suAlphaJetFlux suWeakAlphaJet
  rw [suAlphaJetEquiv.apply_symm_apply, suAlphaCoordinateFlux_apply]
  fin_cases i <;> simp [SUWeakAlphaCoordinate.flux, Fin.sum_univ_two]




theorem SUInitialGain.alpha_flux_weak_derivative
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (ha : alpha ≤ 3 / 2) (a : Fin n) (k i : Fin 2) :
    IntegrableOn (fun x => fderiv ℝ (suAlphaJetFlux g b alpha a k) (suWeakAlphaJet u V x)
      (suWeakAlphaJetColumn V G.hessian i x)) (Metric.ball center (G.radius / 2)) ∧
      HasWeakPartialDeriv i
        (fun x => fderiv ℝ (suAlphaJetFlux g b alpha a k) (suWeakAlphaJet u V x)
          (suWeakAlphaJetColumn V G.hessian i x)) (S.flux a k)
        (Metric.ball center (G.radius / 2)) := by
  let K := (fun x => (x, u x)) '' Metric.closedBall center G.radius
  have hK : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (continuousOn_id.prodMk G.coordinate_continuous)
  have hKt : ∀ x ∈ K, x.2 ∈ (extChartAt (𝓡 n) b).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact S.coordinate_range (Metric.closedBall_subset_closedBall G.radius_lt.le hx)
  obtain ⟨F, C, hF, hC, hb, he⟩ := suAlphaJetFlux_extension g b ha hK hKt
    (if k = 0 then (EuclideanSpace.single a 1, 0) else (0, EuclideanSpace.single a 1))
  have heq (x : LoopPlane) (hx : x ∈ Metric.closedBall center G.radius) :
      F =ᶠ[𝓝 (suWeakAlphaJet u V x)] suAlphaJetFlux g b alpha a k :=
    he (x, u x) (mem_image_of_mem _ hx) (V 0 x, V 1 x)
  obtain ⟨hJ, hW, hw⟩ := G.weak_jet_data
  have hr : 0 < G.radius / 2 := by linarith [G.radius_pos]
  have hrR : G.radius / 2 < G.radius := by linarith [G.radius_pos]
  have hsub := Metric.ball_subset_ball (x := center) hrR.le
  let : IsFiniteMeasure (volume.restrict (Metric.ball center G.radius)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball center G.radius) < ⊤)⟩
  have hi := (suQuadraticDerivative_integrable hJ (hW i) hF hC hb).mono_measure
    (Measure.restrict_mono hsub le_rfl)
  have hd := suWeakPartial_comp_quadratic hr hrR hJ hW hw hF hC hb i
  have hg : (fun x => fderiv ℝ F (suWeakAlphaJet u V x) (suWeakAlphaJetColumn V G.hessian i x))
      =ᵐ[volume.restrict (Metric.ball center (G.radius / 2))]
        fun x => fderiv ℝ (suAlphaJetFlux g b alpha a k) (suWeakAlphaJet u V x)
          (suWeakAlphaJetColumn V G.hessian i x) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [(heq x (Metric.ball_subset_closedBall (hsub hx))).fderiv_eq]
  refine ⟨hi.congr hg, suWeakPartial_congr_ae hd ?_ hg.symm⟩
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  rw [← S.jet_flux_eq a k x]
  exact (heq x (Metric.ball_subset_closedBall (hsub hx))).self_of_nhds.symm




theorem SUInitialGain.alpha_flux_equation_ae
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (ha : 1 ≤ alpha) (ha' : alpha ≤ 3 / 2) :
    ∀ᵐ x ∂volume.restrict (Metric.ball center (G.radius / 2)), ∀ a : Fin n,
      (∑ i : Fin 2, fderiv ℝ (suAlphaJetFlux g b alpha a i) (suWeakAlphaJet u V x)
        (suWeakAlphaJetColumn V G.hessian i x)) + S.sourceTerm a x = 0 := by
  let r := G.radius / 2
  have hrR : r ≤ R := (half_le_self G.radius_pos.le).trans G.radius_lt.le
  have hsub := Metric.ball_subset_ball (x := center) hrR
  let : IsFiniteMeasure (volume.restrict (Metric.ball center R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball center R) < ⊤)⟩
  obtain ⟨hflux, hsource⟩ := S.flux_source_memLp_of_one_le ha
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * alpha / (2 * alpha - 1)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (by linarith : 0 < 2 * alpha - 1)).mpr
    linarith
  rw [ae_all_iff]
  intro a
  apply suWeakDivergence_eq_ae Metric.isOpen_ball
    (fun i => ((hflux a i).integrable hp).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun i => (G.alpha_flux_weak_derivative S ha' a i i).1)
    ((hsource a).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun i => (G.alpha_flux_weak_derivative S ha' a i i).2)
  intro phi hphi hc hs
  have heq := S.scalar_equation ha a hphi hc (hs.trans hsub)
  have hD (x : LoopPlane) (hx : x ∉ Metric.ball center r) (i : Fin 2) :
      fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
      (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
  have hp0 (x : LoopPlane) (hx : x ∉ Metric.ball center r) : phi x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  rwa [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      (fun x hx => by simp only [hD x hx.2, mul_zero, Finset.sum_const_zero]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
      (fun x hx => by rw [hp0 x hx.2, mul_zero])] at heq

end PoincareConjecture.M60

end
