import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessSequence
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitWeak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

local instance suBubbleEquationBilinearNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suBubbleEquationBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance suBubbleEquationTrilinearNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance suBubbleEquationTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 3200000 in

theorem suNormalized_limit_weakCoordinate
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (center : ℕ → UnitTwoSphere) (scale : ℕ → ℝ)
    (hs : ∀ j, 0 < scale j ∧ scale j ≤ 1) {s0 : ℝ}
    (hscale : Tendsto scale atTop (𝓝 s0))
    (v0 : C(LoopPlane, M)) (hv0 : ContMDiff (𝓡 2) (𝓡 n) 1 v0)
    (hlim : Tendsto (fun j => (⟨(fun z =>
        f j ((chartAt LoopPlane (center j)).symm (scale j • z))),
      ((hf j).comp ((suSphereChart_smooth (center j)).comp
        (contDiff_id.const_smul (scale j)).contMDiff)).continuous⟩ : C(LoopPlane, M)))
      atTop (𝓝 v0))
    (hvalues : TendstoLocallyUniformly (fun j z =>
      e (f j ((chartAt LoopPlane (center j)).symm (scale j • z)))) (e ∘ v0) atTop)
    (hderiv : TendstoLocallyUniformly (fun j => fderiv ℝ (fun z =>
      e (f j ((chartAt LoopPlane (center j)).symm (scale j • z)))))
      (fderiv ℝ (e ∘ v0)) atTop)
    (henergy : ∀ j z, m60EnergyDensity g
      (fun y => f j ((chartAt LoopPlane (center j)).symm (scale j • y))) z ≤ 1 / 2)
    (hq : ∀ j z, 2 * m60EnergyDensity g
      (fun y => f j ((chartAt LoopPlane (center j)).symm (scale j • y))) z /
        suAlphaRoundFactor (scale j • z) ∈ Icc 0 1) (a : LoopPlane) :
    ∃ (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E) (R : ℝ), 0 < R ∧
      (∀ z ∈ Metric.closedBall a R, v0 z ∈ (extChartAt (𝓡 n) p).source ∧
        (fun q => L (e q)) =ᶠ[𝓝 (v0 z)] extChartAt (𝓡 n) p) ∧
      let u := fun z => L (e (v0 z))
      SUWeakAlphaCoordinate g p 1 u (fun i z => fderiv ℝ u z (b i)) a R := by
  let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
  have hv (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (v j) :=
    (hf j).comp ((suSphereChart_smooth (center j)).comp
      (contDiff_id.const_smul (scale j)).contMDiff)
  obtain ⟨p, L, r, R, hr, hR, hKt, hchart0, htail⟩ := suC0_common_readable_chart e hread
    (fun j => (⟨v j, (hv j).continuous⟩ : C(LoopPlane, M))) v0 hlim a
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let K := Metric.closedBall ((extChartAt (𝓡 n) p) (v0 a)) r
  let U := fun j z => L (e (v (j + N) z))
  let U0 := fun z => L (e (v0 z))
  let lambda := fun j z => suAlphaRoundFactor (scale (j + N) • z)
  let lambda0 := fun z => suAlphaRoundFactor (s0 • z)
  let rho := fun j => scale (j + N)
  let c := fun j => alpha (j + N) - 1
  let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  have hshift : Tendsto (fun j : ℕ => j + N) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun j => by omega)).tendsto_atTop
  have hU (j : ℕ) : ContDiff ℝ ∞ (U j) :=
    L.contDiff.comp (contMDiff_iff_contDiff.mp (he.comp (hv (j + N))))
  have hU0 : ContDiff ℝ 1 U0 :=
    L.contDiff.comp (contMDiff_iff_contDiff.mp ((he.of_le (by simp)).comp hv0))
  have hchart (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) :=
    hN (j + N) (Nat.le_add_left _ _) z hz
  have htarget (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) : U j z ∈ K := by
    have hx := hchart j z hz
    have heq : U j z = (extChartAt (𝓡 n) p) (v (j + N) z) := hx.2.2.self_of_nhds
    rw [heq]
    exact Metric.ball_subset_closedBall hx.2.1
  have htarget0 (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) : U0 z ∈ K := by
    have hx := hchart0 z hz
    have heq : U0 z = (extChartAt (𝓡 n) p) (v0 z) := hx.2.2.self_of_nhds
    rw [heq]
    exact Metric.ball_subset_closedBall hx.2.1
  have hdU (j : ℕ) (z : LoopPlane) :
      fderiv ℝ (U j) z = L.comp (fderiv ℝ (e ∘ v (j + N)) z) :=
    (L.hasFDerivAt.comp z
      (((contMDiff_iff_contDiff.mp (he.comp (hv (j + N)))).differentiable
        (by simp)) z).hasFDerivAt).fderiv
  have hdU0 (z : LoopPlane) : fderiv ℝ U0 z = L.comp (fderiv ℝ (e ∘ v0) z) :=
    (L.hasFDerivAt.comp z
      ((contMDiff_iff_contDiff.mp ((he.of_le (by simp)).comp hv0)).differentiable_one
        z).hasFDerivAt).fderiv
  have hUl (z : LoopPlane) : Tendsto (fun j => U j z) atTop (𝓝 (U0 z)) :=
    (L.continuous.tendsto _).comp
      ((hvalues.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).comp hshift)
  have hdUl (z : LoopPlane) :
      Tendsto (fun j => fderiv ℝ (U j) z) atTop (𝓝 (fderiv ℝ U0 z)) := by
    have hcomp : Continuous (fun A : LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin d) => L.comp A) :=
      continuous_const.clm_comp continuous_id
    have h := (hcomp.tendsto (fderiv ℝ (e ∘ v0) z)).comp
      ((hderiv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)).comp hshift)
    simpa only [hdU, hdU0, v, Function.comp_def] using! h
  have hlambda (j : ℕ) : ContDiff ℝ ∞ (lambda j) :=
    suRoundFactor_smooth_pos.1.comp (contDiff_id.const_smul (scale (j + N)))
  have hll (z : LoopPlane) : Tendsto (fun j => lambda j z) atTop (𝓝 (lambda0 z)) :=
    (suRoundFactor_smooth_pos.1.continuous.tendsto _).comp
      ((hscale.comp hshift).smul_const z)
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, Function.comp_apply, sub_self] using (ha.comp hshift).sub_const 1
  have hG (y : E) (hy : y ∈ K) : ContDiffAt ℝ ∞ G y :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hKt hy))
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn
    (show ContinuousOn G K from fun y hy => (hG y hy).continuousAt.continuousWithinAt)
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn
    (show ContinuousOn (fderiv ℝ G) K from fun y hy =>
      ((hG y hy).fderiv_right (m := ∞) (by simp)).continuousAt.continuousWithinAt)
  let C := max 0 (max C0 C1)
  have hC : 0 ≤ C := le_max_left _ _
  have hcoeff (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball a R) :
      ‖G (U j z)‖ ≤ C ∧ ‖fderiv ℝ G (U j z)‖ ≤ C := by
    have hx := htarget j z (Metric.ball_subset_closedBall hz)
    exact ⟨(hC0 _ hx).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hC1 _ hx).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  obtain ⟨B, hB, hd⟩ := exists_observed_derivative_energy_bound g e (he.of_le (by simp))
  let D := ‖L‖ * Real.sqrt (2 * B)
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hgrad (j : ℕ) (z : LoopPlane) (i : Fin 2) : ‖fderiv ℝ (U j) z (b i)‖ ≤ D := by
    have h0 := hd (v (j + N)) ((hv (j + N)).of_le (by simp)) z 0
    have h1 := hd (v (j + N)) ((hv (j + N)).of_le (by simp)) z 1
    have hop := plane_opNorm_sq_le (fderiv ℝ (e ∘ v (j + N)) z)
    have hnorm : ‖fderiv ℝ (e ∘ v (j + N)) z‖ ≤ Real.sqrt (2 * B) := by
      have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * B by positivity)
      nlinarith [mul_le_mul_of_nonneg_left (henergy (j + N) z) hB,
        norm_nonneg (fderiv ℝ (e ∘ v (j + N)) z), Real.sqrt_nonneg (2 * B)]
    rw [hdU, ContinuousLinearMap.comp_apply]
    calc
      _ ≤ ‖L‖ * ‖fderiv ℝ (e ∘ v (j + N)) z (b i)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖fderiv ℝ (e ∘ v (j + N)) z‖ * ‖b i‖) := by
        gcongr
        exact (fderiv ℝ (e ∘ v (j + N)) z).le_opNorm _
      _ ≤ D := by simpa only [OrthonormalBasis.norm_eq_one, mul_one] using
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg L)
  have hql (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball a R) :
      (∑ i : Fin 2, G (U j z) (fderiv ℝ (U j) z (b i))
        (fderiv ℝ (U j) z (b i))) / lambda j z ∈ Icc 0 1 := by
    have hx := hchart j z (Metric.ball_subset_closedBall hz)
    have h := suChartReader_energy g e p L (v (j + N)) ((hv (j + N)).of_le (by simp))
      z hx.1 hx.2.2
    change 2 * m60EnergyDensity g (v (j + N)) z = _ at h
    rw [← h]
    exact hq (j + N) z
  have hequation (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball a R) :
      let Gamma := CoordinateExponential.christoffelBilinear G
      let w := fun y => ((rho j) ^ 2 + (∑ i : Fin 2,
        G (U j y) (fderiv ℝ (U j) y (b i)) (fderiv ℝ (U j) y (b i))) /
          lambda j y) ^ (c j)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma (U j)
        (fun y => w y • fderiv ℝ (U j) y (b i)) (b i) z = 0 := by
    have hx := hchart j z (Metric.ball_subset_closedBall hz)
    apply suChartReader_weightedEuler g e p L (v (j + N)) ((hv (j + N)).of_le (by simp))
      (lambda j) (rho j) (c j) z hx.1 hx.2.2
    simpa only [v, lambda, rho, c, zero_add] using
      suSphereWeightedEuler_rescale g (hf (j + N)) (heq (j + N))
        (center (j + N)) 0 (scale (j + N)) p z
        (by simpa only [zero_add, v, ContinuousMap.coe_mk] using hx.1)
  refine ⟨p, L, R, hR, (fun z hz => ⟨(hchart0 z hz).1, (hchart0 z hz).2.2⟩), ?_⟩
  apply suC1_harmonic_weakCoordinate g p U0 hU0 a hR
    (fun z hz => hKt (htarget0 z hz))
  intro phi hp hcpt hsupport
  exact suWeightedEuler_limit_variation g p U U0 lambda lambda0 rho c a hC hD
    (fun j => (hU j).contDiffOn) (fun j => (hlambda j).contDiffOn)
    (fun j z hz => hKt (htarget j z (Metric.ball_subset_closedBall hz)))
    (fun z hz => hKt (htarget0 z (Metric.ball_subset_closedBall hz)))
    (fun z _ => hUl z) (fun z _ => hdUl z) (fun z _ => hll z)
    (fun z _ => suRoundFactor_smooth_pos.2 _) (fun j z _ => suRoundFactor_smooth_pos.2 _)
    (hscale.comp hshift) (fun j => (hs (j + N)).1) (fun j => (hs (j + N)).2) hc
    (fun j => sub_nonneg.mpr (har (j + N)).1)
    (fun j => by dsimp only [c]; linarith [(har (j + N)).2])
    hcoeff (fun j z _ => hgrad j z) hql hequation phi hp hcpt hsupport

end PoincareConjecture.M60
