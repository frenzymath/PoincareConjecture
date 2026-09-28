import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalWeakEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessEquation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerRoundFactor
import PoincareConjecture.Proofs.M60.Mathlib.CovariantIntegrationByParts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Manifold

noncomputable section

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation ConjugateVariation
  Poincare.Riemannian.RadialTransport

local instance suNormalizedEquationBilinearGroup {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance suNormalizedEquationBilinearSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem suMetricQuadratic_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : P → E) (v : Fin 2 → P → E) (x d : P)
    (hG : DifferentiableAt ℝ G (u x)) (hu : DifferentiableAt ℝ u x)
    (hv : ∀ i, DifferentiableAt ℝ (v i) x)
    (hsym : ∀ a b, G (u x) a b = G (u x) b a) :
    fderiv ℝ (fun y => ∑ i : Fin 2, G (u y) (v i y) (v i y)) x d =
      (∑ i : Fin 2, fderiv ℝ G (u x) (fderiv ℝ u x d) (v i x) (v i x)) +
        2 * ∑ i : Fin 2, G (u x) (v i x) (fderiv ℝ (v i) x d) := by
  have hGu := hG.hasFDerivAt.comp x hu.hasFDerivAt
  have hq := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hGu.clm_apply (hv i).hasFDerivAt).clm_apply (hv i).hasFDerivAt)
  have hqd := hq.fderiv
  simp only [Function.comp_apply] at hqd
  rw [hqd]
  simp only [Fin.sum_univ_two, add_apply, coe_comp, Function.comp_apply, flip_apply]
  rw [hsym (fderiv ℝ (v 0) x d), hsym (fderiv ℝ (v 1) x d)]
  ring

theorem suWeightedMetricFlux_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : P → E) (v : Fin 2 → P → E)
    (lambda : P → ℝ) (x d : P) (w : E) (k : Fin 2) (alpha : ℝ)
    (hG : DifferentiableAt ℝ G (u x)) (hu : DifferentiableAt ℝ u x)
    (hv : ∀ i, DifferentiableAt ℝ (v i) x) (hl : DifferentiableAt ℝ lambda x)
    (hlpos : 0 < lambda x) (hsym : ∀ a b, G (u x) a b = G (u x) b a)
    (hpos : ∀ a, 0 ≤ G (u x) a a) :
    let Q := fun y => ∑ i : Fin 2, G (u y) (v i y) (v i y)
    fderiv ℝ (fun y => 2 * alpha * (1 + Q y / lambda y) ^ (alpha - 1) *
      G (u y) (v k y) w) x d =
      (2 * alpha * (1 + Q x / lambda x) ^ (alpha - 1)) *
        (fderiv ℝ G (u x) (fderiv ℝ u x d) (v k x) w +
          G (u x) (fderiv ℝ (v k) x d) w +
          (alpha - 1) / (lambda x + Q x) *
            ((∑ i : Fin 2, fderiv ℝ G (u x) (fderiv ℝ u x d) (v i x) (v i x)) +
              2 * ∑ i : Fin 2, G (u x) (v i x) (fderiv ℝ (v i) x d) -
              Q x * fderiv ℝ lambda x d / lambda x) * G (u x) (v k x) w) := by
  let Q := fun y => ∑ i : Fin 2, G (u y) (v i y) (v i y)
  let a := fun y => 1 + Q y / lambda y
  have hQ : DifferentiableAt ℝ Q x := DifferentiableAt.fun_sum (u := Finset.univ)
    (fun i _ => (((hG.comp x hu).clm_apply (hv i)).clm_apply (hv i)))
  have hlinv := (hasDerivAt_inv hlpos.ne').comp_hasFDerivAt x hl.hasFDerivAt
  have haD := (hasFDerivAt_const (1 : ℝ) x).add (hQ.hasFDerivAt.mul hlinv)
  have ha : DifferentiableAt ℝ a x := by
    simpa only [a, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! haD.differentiableAt
  have hQpos : 0 ≤ Q x := Finset.sum_nonneg fun i _ => hpos _
  have hapos : 0 < a x := by dsimp [a]; positivity
  have hdpos : 0 < lambda x + Q x := add_pos_of_pos_of_nonneg hlpos hQpos
  have hweight := ha.hasFDerivAt.rpow_const (p := alpha - 1) (Or.inl hapos.ne')
  have hpair := ((hG.hasFDerivAt.comp x hu.hasFDerivAt).clm_apply
    (hv k).hasFDerivAt).clm_apply (hasFDerivAt_const w x)
  have hflux := ((hweight.const_mul (2 * alpha)).mul hpair).fderiv
  simp only [Function.comp_apply] at hflux
  have hp : a x ^ (alpha - 1 - 1) = a x ^ (alpha - 1) / a x := by
    rw [Real.rpow_sub hapos, Real.rpow_one]
  have had' : fderiv ℝ a x d =
      (fderiv ℝ Q x d * lambda x - Q x * fderiv ℝ lambda x d) / lambda x ^ 2 := by
    have he : a = fun y => 1 + Q y * ((fun t : ℝ => t⁻¹) ∘ lambda) y := by
      funext y
      simp only [a, div_eq_mul_inv, Function.comp_apply]
    rw [he]
    change (fderiv ℝ ((fun _ : P => (1 : ℝ)) + Q * ((fun t : ℝ => t⁻¹) ∘ lambda)) x) d = _
    rw [haD.fderiv]
    simp only [add_apply, zero_add, smul_apply, smul_eq_mul, Function.comp_apply]
    field_simp
    ring
  dsimp only
  change fderiv ℝ ((fun y => 2 * alpha * a y ^ (alpha - 1)) *
    (fun y => G (u y) (v k y) w)) x d = _
  rw [hflux]
  simp only [add_apply, smul_apply, smul_eq_mul, coe_comp, Function.comp_apply,
    flip_apply, zero_apply, map_zero, zero_add]
  rw [hp, had', suMetricQuadratic_fderiv G u v x d hG hu hv hsym]
  change _ = (2 * alpha * a x ^ (alpha - 1)) * _
  dsimp only [a, Q] at hdpos ⊢
  field_simp [hlpos.ne', hdpos.ne']
  ring

theorem suWeightedLinearMetricFlux_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : P →L[ℝ] E) (v : Fin 2 → P →L[ℝ] E)
    (lambda : P → ℝ) (x d : P) (w : E) (k : Fin 2) (alpha : ℝ)
    (hG : DifferentiableAt ℝ G (u x)) (hl : DifferentiableAt ℝ lambda x)
    (hlpos : 0 < lambda x) (hsym : ∀ a b, G (u x) a b = G (u x) b a)
    (hpos : ∀ a, 0 ≤ G (u x) a a) :
    let Q := fun y => ∑ i : Fin 2, G (u y) (v i y) (v i y)
    fderiv ℝ (fun y => 2 * alpha * (1 + Q y / lambda y) ^ (alpha - 1) *
      G (u y) (v k y) w) x d =
      (2 * alpha * (1 + Q x / lambda x) ^ (alpha - 1)) *
        (fderiv ℝ G (u x) (u d) (v k x) w + G (u x) (v k d) w +
          (alpha - 1) / (lambda x + Q x) *
            ((∑ i : Fin 2, fderiv ℝ G (u x) (u d) (v i x) (v i x)) +
              2 * ∑ i : Fin 2, G (u x) (v i x) (v i d) -
              Q x * fderiv ℝ lambda x d / lambda x) * G (u x) (v k x) w) := by
  simpa only [ContinuousLinearMap.fderiv] using
    suWeightedMetricFlux_fderiv G u (fun i => v i) lambda x d w k alpha
      hG u.differentiableAt (fun i => (v i).differentiableAt) hl hlpos hsym hpos

theorem suAlphaJetFlux_fderiv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (a : Fin n) (k i : Fin 2)
    (x : LoopPlane) (y : EuclideanSpace ℝ (Fin n))
    (v : Fin 2 → EuclideanSpace ℝ (Fin n))
    (H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (extChartAt (𝓡 n) b).target) :
    let G := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let Q := ∑ j : Fin 2, G y (v j) (v j)
    fderiv ℝ (suAlphaJetFlux g b alpha a k) (suAlphaJetEquiv.symm ((x, y), (v 0, v 1)))
      (suAlphaJetEquiv.symm ((EuclideanSpace.single i 1, v i), (H 0 i, H 1 i))) =
      (2 * alpha * (1 + Q / suAlphaRoundFactor x) ^ (alpha - 1)) *
        (fderiv ℝ G y (v i) (v k) (EuclideanSpace.single a 1) +
          G y (H k i) (EuclideanSpace.single a 1) +
          (alpha - 1) / (suAlphaRoundFactor x + Q) *
            ((∑ j : Fin 2, fderiv ℝ G y (v i) (v j) (v j)) +
              2 * ∑ j : Fin 2, G y (v j) (H j i) -
              Q * fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1) /
                suAlphaRoundFactor x) *
            G y (v k) (EuclideanSpace.single a 1)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let P := EuclideanSpace ℝ (Fin ((2 + n) + (n + n)))
  let e : P ≃L[ℝ] ((LoopPlane × E) × (E × E)) := suAlphaJetEquiv
  let pp : P →L[ℝ] LoopPlane := (fst ℝ LoopPlane E).comp
    ((fst ℝ (LoopPlane × E) (E × E)).comp e.toContinuousLinearMap)
  let uu : P →L[ℝ] E := (snd ℝ LoopPlane E).comp
    ((fst ℝ (LoopPlane × E) (E × E)).comp e.toContinuousLinearMap)
  let vv : Fin 2 → P →L[ℝ] E := fun j =>
    (if j = 0 then fst ℝ E E else snd ℝ E E).comp
      ((snd ℝ (LoopPlane × E) (E × E)).comp e.toContinuousLinearMap)
  let z := e.symm ((x, y), (v 0, v 1))
  let d := e.symm ((EuclideanSpace.single i 1, v i), (H 0 i, H 1 i))
  let G := g.pullbackCoefficients (chartAt E b).symm
  have hpz : pp z = x := by simp [pp, z]
  have huz : uu z = y := by simp [uu, z]
  have hvz (j : Fin 2) : vv j z = v j := by fin_cases j <;> simp [vv, z]
  have hpd : pp d = EuclideanSpace.single i 1 := by simp [pp, d]
  have hud : uu d = v i := by simp [uu, d]
  have hvd (j : Fin 2) : vv j d = H j i := by fin_cases j <;> simp [vv, d]
  have hG : DifferentiableAt ℝ G (uu z) := by
    rw [huz]
    exact ((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds hy)).differentiableAt (by simp)
  have hpos (w : E) : 0 ≤ G (uu z) w w := by
    change 0 ≤ g.inner ((extChartAt (𝓡 n) b).symm (uu z))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (uu z) w)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (uu z) w)
    by_cases hw : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (uu z) w = 0
    · rw [hw]
      simp
    · exact (g.pos _ _ hw).le
  have hlam : DifferentiableAt ℝ (suAlphaRoundFactor ∘ pp) z :=
    (suRoundFactor_smooth_pos.1.differentiable (by simp) _).comp z pp.differentiableAt
  have hflux := suWeightedLinearMetricFlux_fderiv G uu vv
    (suAlphaRoundFactor ∘ pp) z d (EuclideanSpace.single a 1) k alpha
    hG hlam
    (suRoundFactor_smooth_pos.2 _) (fun _ _ => g.symm _ _ _) hpos
  have hlD : fderiv ℝ (suAlphaRoundFactor ∘ pp) z d =
      fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1) := by
    rw [fderiv_comp z (suRoundFactor_smooth_pos.1.differentiable (by simp) _)
      pp.differentiableAt, pp.fderiv, comp_apply, hpz, hpd]
  have hfun : suAlphaJetFlux g b alpha a k = fun z =>
      2 * alpha * (1 + (∑ j : Fin 2, G (uu z) (vv j z) (vv j z)) /
        suAlphaRoundFactor (pp z)) ^ (alpha - 1) *
          G (uu z) (vv k z) (EuclideanSpace.single a 1) := by
    funext z'
    unfold suAlphaJetFlux
    rw [suAlphaCoordinateFlux_apply]
    fin_cases k <;> simp [vv, pp, uu, G, e, E, Fin.sum_univ_two] <;> rfl
  rw [hfun]
  dsimp only at hflux
  simp only [Function.comp_apply, hpz, hlD] at hflux
  fin_cases k <;> simpa [G, E, z, d, e, uu, vv, Fin.sum_univ_two] using! hflux

theorem suMetricJet_connection_cancellation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (Gamma : E →L[ℝ] E →L[ℝ] E)
    (hs : ∀ v w, B v w = B w v) (ht : ∀ v w, Gamma v w = Gamma w v)
    (hc : ∀ v w z, DG v w z = B (Gamma v w) z + B w (Gamma v z)) (v w : E) :
    2 * DG v v w - DG w v v = 2 * B (Gamma v v) w := by
  rw [hc v v w, hc w v v, ht w v, hs (Gamma v w) v]
  ring

theorem suMetricJet_residual_pairing {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (DG : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (Gamma : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hs : ∀ v w, B v w = B w v) (ht : ∀ v w, Gamma v w = Gamma w v)
    (hc : ∀ v w z, DG v w z = B (Gamma v w) z + B w (Gamma v z))
    (v : Fin 2 → EuclideanSpace ℝ (Fin n))
    (H : Fin 2 → Fin 2 → EuclideanSpace ℝ (Fin n))
    (lambda d c : ℝ) (dlambda : Fin 2 → ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    2 * (∑ i : Fin 2, (DG (v i) (v i) w + B (H i i) w + c / d *
      ((∑ j : Fin 2, DG (v i) (v j) (v j)) +
        2 * ∑ j : Fin 2, B (v j) (H j i) -
        (∑ j : Fin 2, B (v j) (v j)) * dlambda i / lambda) * B (v i) w)) -
      (∑ i : Fin 2, DG w (v i) (v i)) =
        2 * B ((∑ i : Fin 2, H i i) + c • suAlphaHessianTerm B v H d -
          suAlphaLowerTerm Gamma B DG v lambda dlambda d c) w := by
  have h0 := suMetricJet_connection_cancellation B DG Gamma hs ht hc (v 0) w
  have h1 := suMetricJet_connection_cancellation B DG Gamma hs ht hc (v 1) w
  simp only [suAlphaHessianTerm, suAlphaLowerTerm, Fin.sum_univ_two, map_add, map_sub,
    map_neg, map_smul, add_apply, sub_apply, neg_apply, smul_apply, smul_eq_mul]
  linear_combination h0 + h1

set_option maxHeartbeats 1200000 in

theorem SUInitialGain.alpha_normalized_equation_ae
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (G : SUInitialGain u V center R) (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (ha : 1 ≤ alpha) (ha' : alpha ≤ 3 / 2) :
    let B := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
    let Gamma := christoffelBilinear B
    ∀ᵐ x ∂volume.restrict (Metric.ball center (G.radius / 2)),
      let v := fun i => V i x
      let H := fun i j => G.hessian i j x
      let d := suAlphaRoundFactor x + ∑ i : Fin 2, B (u x) (v i) (v i)
      (∑ i : Fin 2, H i i) + (alpha - 1) • suAlphaHessianTerm (B (u x)) v H d =
        suAlphaLowerTerm (Gamma (u x)) (B (u x)) (fderiv ℝ B (u x)) v
          (suAlphaRoundFactor x)
          (fun i => fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1)) d (alpha - 1) := by
  let B := g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm
  let Gamma := christoffelBilinear B
  filter_upwards [G.alpha_flux_equation_ae S ha ha',
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxb
  have hxr : x ∈ Metric.closedBall center R := Metric.ball_subset_closedBall
    (Metric.ball_subset_ball ((half_le_self G.radius_pos.le).trans G.radius_lt.le) hxb)
  have hy := S.coordinate_range hxr
  let v := fun i => V i x
  let H := fun i j => G.hessian i j x
  let Q := ∑ i : Fin 2, B (u x) (v i) (v i)
  let d := suAlphaRoundFactor x + Q
  let dl := fun i => fderiv ℝ suAlphaRoundFactor x (EuclideanSpace.single i 1)
  let T := (∑ i : Fin 2, H i i) + (alpha - 1) • suAlphaHessianTerm (B (u x)) v H d -
    suAlphaLowerTerm (Gamma (u x)) (B (u x)) (fderiv ℝ B (u x)) v
      (suAlphaRoundFactor x) dl d (alpha - 1)
  have hQ : 0 ≤ Q := by
    apply Finset.sum_nonneg
    intro i _
    change 0 ≤ g.inner ((extChartAt (𝓡 n) b).symm (u x))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (u x) (v i))
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (u x) (v i))
    by_cases h : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (u x) (v i) = 0
    · rw [h]
      simp
    · exact (g.pos _ _ h).le
  have hp : 0 < alpha * (1 + Q / suAlphaRoundFactor x) ^ (alpha - 1) :=
    mul_pos (by linarith) (Real.rpow_pos_of_pos (by
      have := div_nonneg hQ (suRoundFactor_smooth_pos.2 x).le
      linarith) _)
  have hcomp := isMetricCompatibleAt_chartCoefficients g b hy
  have hpair (a : Fin n) : B (u x) T (EuclideanSpace.single a 1) = 0 := by
    have he := hx a
    change (∑ i : Fin 2, fderiv ℝ (suAlphaJetFlux g b alpha a i)
      (suAlphaJetEquiv.symm ((x, u x), (v 0, v 1)))
      (suAlphaJetEquiv.symm ((EuclideanSpace.single i 1, v i), (H 0 i, H 1 i)))) +
        S.sourceTerm a x = 0 at he
    simp_rw [suAlphaJetFlux_fderiv g b alpha a _ _ x (u x) v H hy] at he
    have hid := suMetricJet_residual_pairing (B (u x)) (fderiv ℝ B (u x)) (Gamma (u x))
      (fun _ _ => g.symm _ _ _) (christoffelBilinear_chart_symm g b (u x)) hcomp
      v H (suAlphaRoundFactor x) d (alpha - 1) dl (EuclideanSpace.single a 1)
    have hz : (alpha * (1 + Q / suAlphaRoundFactor x) ^ (alpha - 1)) *
        (2 * B (u x) T (EuclideanSpace.single a 1)) = 0 := by
      rw [← hid]
      dsimp only [SUWeakAlphaCoordinate.sourceTerm, Q, d, dl, B, v] at he ⊢
      simp only [Fin.sum_univ_two] at he ⊢
      linear_combination he
    exact (mul_eq_zero.mp hz).resolve_left hp.ne' |> fun h => by linarith
  have hT : T = 0 := by
    apply (g.isInvertible_chartCoefficients b hy).injective
    ext w
    have hw : (∑ a : Fin n, w a • EuclideanSpace.single a (1 : ℝ)) = w := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
    change B (u x) T w = (B (u x) 0) w
    rw [← hw]
    simp only [map_sum, map_smul, hpair, smul_zero, Finset.sum_const_zero, map_zero, zero_apply]
  exact sub_eq_zero.mp hT

end PoincareConjecture.M60

end
