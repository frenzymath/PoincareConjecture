import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessCharts
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessLocalEstimate
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessNormalization



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

set_option maxHeartbeats 2400000 in






theorem suNormalized_local_equations
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hread : SUChartReadable (n := n) e)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (center : ℕ → UnitTwoSphere) (scale : ℕ → ℝ)
    (hs : ∀ j, 0 < scale j ∧ scale j ≤ 1)
    (v0 : C(LoopPlane, M)) {C : ℝ} (hC : 0 ≤ C)
    (hlim : Tendsto (fun j => (⟨(fun z =>
        f j ((chartAt LoopPlane (center j)).symm (scale j • z))),
      ((hf j).comp ((suSphereChart_smooth (center j)).comp
        (contDiff_id.const_smul (scale j)).contMDiff)).continuous⟩ : C(LoopPlane, M)))
      atTop (𝓝 v0))
    (hgrad : ∀ j z, ‖fderiv ℝ
      (fun y => e (f j ((chartAt LoopPlane (center j)).symm (scale j • y)))) z‖ ≤ C)
    (a : LoopPlane) :
    ∃ (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E) (r t : ℝ) (N : ℕ) (A F : ℝ),
      0 < r ∧ 0 < t ∧ 0 ≤ A ∧ 0 ≤ F ∧
      Metric.closedBall ((extChartAt (𝓡 n) p) (v0 a)) r ⊆ (extChartAt (𝓡 n) p).target ∧
      let v := fun j z => f (j + N)
        ((chartAt LoopPlane (center (j + N))).symm (scale (j + N) • z))
      (∀ j x, x ∈ Metric.closedBall a (4 * t) →
        v j x ∈ (extChartAt (𝓡 n) p).source ∧
        (extChartAt (𝓡 n) p) (v j x) ∈
          Metric.closedBall ((extChartAt (𝓡 n) p) (v0 a)) r ∧
        (fun q => L (e q)) =ᶠ[𝓝 (v j x)] extChartAt (𝓡 n) p) ∧
      let U := fun j z => L (e (v j (a + t • z)))
      let lambda := fun j z => suAlphaRoundFactor (scale (j + N) • (a + t • z))
      let rho := fun j => scale (j + N) * t
      let c := fun j => alpha (j + N) - 1
      (∀ j, ContDiff ℝ ∞ (U j)) ∧
      (∀ j z, z ∈ Metric.ball (0 : LoopPlane) 2 → ‖U j z‖ ≤ A ∧
        ∀ i : Fin 2, ‖fderiv ℝ (U j) z (b i)‖ ≤ A) ∧
      (∀ j z, z ∈ Metric.ball (0 : LoopPlane) 2 →
        ‖suNormalizedAlphaCoordinateSource g p (U j) (lambda j) (rho j) (c j) z‖ ≤ F) ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ j in atTop, ∀ z ∈ Metric.ball (0 : LoopPlane) 2,
        ‖(∑ i : Fin 2, suCoordinateHessian (U j) z i i) -
          suNormalizedAlphaCoordinateSource g p (U j) (lambda j) (rho j) (c j) z‖ ≤
          delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, ‖suCoordinateHessian (U j) z i k‖ ^ 2) := by
  let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
  have hv (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (v j) :=
    (hf j).comp ((suSphereChart_smooth (center j)).comp
      (contDiff_id.const_smul (scale j)).contMDiff)
  obtain ⟨p, L, r, R, hr, hR, hK, -, htail⟩ := suC0_common_readable_chart e hread
    (fun j => (⟨v j, (hv j).continuous⟩ : C(LoopPlane, M))) v0 hlim a
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let t := R / 4
  have ht : 0 < t := by dsimp [t]; positivity
  have hRt : 4 * t = R := by dsimp [t]; ring
  let K := Metric.closedBall ((extChartAt (𝓡 n) p) (v0 a)) r
  have hgood (j : ℕ) (x : LoopPlane) (hx : x ∈ Metric.closedBall a (4 * t)) :
      v (j + N) x ∈ (extChartAt (𝓡 n) p).source ∧
      (extChartAt (𝓡 n) p) (v (j + N) x) ∈
        Metric.ball ((extChartAt (𝓡 n) p) (v0 a)) r ∧
      (fun q => L (e q)) =ᶠ[𝓝 (v (j + N) x)] extChartAt (𝓡 n) p :=
    hN (j + N) (Nat.le_add_left _ _) x (by rwa [hRt] at hx)
  have himage (z : LoopPlane) (hz : z ∈ Metric.closedBall (0 : LoopPlane) 2) :
      a + t • z ∈ Metric.closedBall a (4 * t) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.le]
    have hzn : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  let U := fun j z => L (e (v (j + N) (a + t • z)))
  let lambda := fun j z => suAlphaRoundFactor (scale (j + N) • (a + t • z))
  let rho := fun j => scale (j + N) * t
  let c := fun j => alpha (j + N) - 1
  have hU (j : ℕ) : ContDiff ℝ ∞ (U j) := L.contDiff.comp
    ((contMDiff_iff_contDiff.mp (he.comp (hv (j + N)))).comp
      (contDiff_const.add (contDiff_id.const_smul t)))
  have hlambda (j : ℕ) : ContDiff ℝ ∞ (lambda j) :=
    suRoundFactor_smooth_pos.1.comp
      ((contDiff_const.add (contDiff_id.const_smul t)).const_smul (scale (j + N)))
  have htarget (j : ℕ) : MapsTo (U j) (Metric.ball (0 : LoopPlane) 2) K := by
    intro z hz
    have h := hgood j (a + t • z) (himage z (Metric.ball_subset_closedBall hz))
    change L (e (v (j + N) (a + t • z))) ∈ K
    have hvalue : L (e (v (j + N) (a + t • z))) =
        (extChartAt (𝓡 n) p) (v (j + N) (a + t • z)) := h.2.2.self_of_nhds
    rw [hvalue]
    exact Metric.ball_subset_closedBall h.2.1
  let D := ‖L‖ * t * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDU (j : ℕ) (z : LoopPlane) (i : Fin 2) : ‖fderiv ℝ (U j) z (b i)‖ ≤ D := by
    let W := fun y => e (v (j + N) (a + t • y))
    have hW : DifferentiableAt ℝ W z :=
      (((contMDiff_iff_contDiff.mp (he.comp (hv (j + N)))).comp
        (contDiff_const.add (contDiff_id.const_smul t))).differentiable (by simp)) z
    have hderiv : fderiv ℝ (U j) z = L.comp (fderiv ℝ W z) :=
      (L.hasFDerivAt.comp z hW.hasFDerivAt).fderiv
    rw [hderiv, ContinuousLinearMap.comp_apply]
    have hWd : fderiv ℝ W z = t • fderiv ℝ (e ∘ v (j + N)) (a + t • z) :=
      suRescale_fderiv (e ∘ v (j + N)) a t z
    rw [hWd, smul_apply]
    calc
      _ ≤ ‖L‖ * ‖t • (fderiv ℝ (e ∘ v (j + N)) (a + t • z)) (b i)‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (t * C) := by
        rw [norm_smul, Real.norm_of_nonneg ht.le]
        gcongr
        calc
          _ ≤ ‖fderiv ℝ (e ∘ v (j + N)) (a + t • z)‖ * ‖b i‖ :=
            (fderiv ℝ (e ∘ v (j + N)) (a + t • z)).le_opNorm _
          _ ≤ C := by
            simpa only [v, Function.comp_def, OrthonormalBasis.norm_eq_one, mul_one]
              using hgrad (j + N) (a + t • z)
      _ = D := by dsimp [D]; ring
  obtain ⟨Ls, Ns, hLs, hNs, hsource⟩ := suRescaledRoundFactor_compact_bounds a t 2
  have hl (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 2) :
      0 < lambda j z ∧ (lambda j z)⁻¹ ≤ Ls :=
    ⟨suRoundFactor_smooth_pos.2 _, (hsource (scale (j + N))
      ⟨(hs (j + N)).1.le, (hs (j + N)).2⟩ z (Metric.ball_subset_closedBall hz)).1⟩
  have hdl (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 2) (i : Fin 2) :
      ‖fderiv ℝ (lambda j) z (b i)‖ ≤ Ns := by
    calc
      _ ≤ ‖fderiv ℝ (lambda j) z‖ * ‖b i‖ := (fderiv ℝ (lambda j) z).le_opNorm _
      _ ≤ Ns := by
        simpa only [lambda, OrthonormalBasis.norm_eq_one, mul_one] using
          (hsource (scale (j + N)) ⟨(hs (j + N)).1.le, (hs (j + N)).2⟩
          z (Metric.ball_subset_closedBall hz)).2
  have hc : Tendsto c atTop (𝓝 0) := by
    have hshift : Tendsto (fun j : ℕ => j + N) atTop atTop :=
      (strictMono_nat_of_lt_succ (fun j => by omega)).tendsto_atTop
    simpa only [c, Function.comp_apply, sub_self] using (ha.comp hshift).sub_const 1
  have hequation (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 2) :
      let G := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      let Gamma := CoordinateExponential.christoffelBilinear G
      let w := fun y => ((rho j) ^ 2 + (∑ i : Fin 2,
        G (U j y) (fderiv ℝ (U j) y (b i)) (fderiv ℝ (U j) y (b i))) /
          lambda j y) ^ (c j)
      ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma (U j)
        (fun y => w y • fderiv ℝ (U j) y (b i)) (b i) z = 0 := by
    let F := fun y => v (j + N) (a + t • y)
    have hF : ContMDiff (𝓡 2) (𝓡 n) ∞ F :=
      (hv (j + N)).comp (contDiff_const.add (contDiff_id.const_smul t)).contMDiff
    have h := hgood j (a + t • z) (himage z (Metric.ball_subset_closedBall hz))
    apply suChartReader_weightedEuler g e p L F (hF.of_le (by simp))
      (lambda j) (rho j) (c j) z h.1 h.2.2
    have hbase := suSphereWeightedEuler_rescale g (hf (j + N)) (heq (j + N))
      (center (j + N)) (scale (j + N) • a) (scale (j + N) * t) p z
      (by simpa only [v, smul_add, smul_smul] using h.1)
    simpa only [F, v, lambda, rho, c, smul_add, smul_smul] using hbase
  obtain ⟨A, F, hA, hF, hjet, hforcing, hresidual⟩ := suAlphaChart_uniform_nearLaplacian
    g p (isCompact_closedBall _ _) hK U lambda rho c 0 hD hLs hNs
    (fun j => (hU j).contDiffOn) (fun j => (hlambda j).contDiffOn) htarget
    (fun j z _ i => hDU j z i) hl hdl (fun j => mul_pos (hs (j + N)).1 ht) hc
    (fun j => sub_nonneg.mpr (har (j + N)).1) (fun j => by dsimp [c]; linarith [(har (j + N)).2])
    hequation
  refine ⟨p, L, r, t, N, A, F, hr, ht, hA, hF, hK, ?_, hU, hjet, hforcing, hresidual⟩
  intro j x hx
  have h := hgood j x hx
  exact ⟨h.1, Metric.ball_subset_closedBall h.2.1, h.2.2⟩

end PoincareConjecture.M60
