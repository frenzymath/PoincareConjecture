import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CoordinateCore
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SourceEmbedding.MetricExhaustion











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

universe u v

namespace PoincareConjecture.M28

set_option maxHeartbeats 800000 in




theorem eventually_source_core_subset_image
    {n : ℕ} {Q : Type v} {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    [Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (e : ∀ k, ball (0 : EuclideanSpace ℝ (Fin n)) 1 → M k)
    (q : ball (0 : EuclideanSpace ℝ (Fin n)) 1 → Q) (F : ∀ k, Q → M k)
    {L : ℝ≥0} (he : ∀ k, LipschitzWith L (e k))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ k x y, c * dist x y ≤ dist (e k x) (e k y))
    (hopen : ∀ k, Topology.IsOpenEmbedding (e k))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth :
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n))
          (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (happrox : ∀ C, IsCompact C → TendstoUniformlyOn
      (fun k x => dist (F k (q x)) (e k x)) (fun _ => 0) atTop C)
    (hFsmooth : ∀ᶠ k in atTop, ContMDiffOn (𝓡 n) (𝓡 n) ∞
      (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
        (fun _ => isOpen_ball) (i := 0) (F k ∘ q)) (closedBall 0 (3 / 4)))
    (hjet : ∀ m, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
      (ChartDistance.coordinateRepresentative (fun _ : ℕ => ball 0 1)
        (fun _ => isOpen_ball) (i := 0) (j := 0)
          (fun x => Function.invFun (e k) (F k (q x)))))
      (iteratedFDeriv ℝ m id) atTop (closedBall 0 (1 / 2)))
    (A : Set Q)
    (hA : q '' {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
      x.val ∈ closedBall 0 (1 / 2)} ⊆ A) :
    ∀ᶠ k in atTop, e k '' {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
      x.val ∈ closedBall 0 (1 / 4)} ⊆ F k '' A := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let U : ℕ → Set E := fun _ => ball 0 1
  let : LocallyCompactSpace (ball (0 : E) 1) := isOpen_ball.locallyCompactSpace
  let C : Set (ball (0 : E) 1) := {x | x.val ∈ closedBall 0 (3 / 4)}
  have hCU : closedBall (0 : E) (3 / 4) ⊆ ball 0 1 :=
    closedBall_subset_ball (by norm_num)
  have hC : IsCompact C := by
    apply isOpen_ball.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
      (isCompact_closedBall 0 (3 / 4))
    intro x hx
    exact ⟨⟨x, hCU hx⟩, rfl⟩
  have hreach := ChartDistance.eventually_mem_range_of_uniform_chart_approximation
    he hc hlower hopen hconn hC (happrox C hC)
  let a : ℕ → E → E := fun k => ChartDistance.coordinateRepresentative U
    (fun _ => isOpen_ball) (i := 0) (j := 0)
      (fun x => Function.invFun (e k) (F k (q x)))
  have hdiff : ∀ᶠ k in atTop, ∀ x ∈ closedBall (0 : E) (1 / 2),
      DifferentiableAt ℝ (a k) x := by
    filter_upwards [hFsmooth, hreach] with k hk hr x hx
    have hxB : x ∈ ball (0 : E) (3 / 4) :=
      closedBall_subset_ball (by norm_num) hx
    have hxU : x ∈ ball (0 : E) 1 := hCU (ball_subset_closedBall hxB)
    let xp : Piece U 0 := ⟨x, hxU⟩
    have hxpC : xp ∈ C := by
      change x ∈ closedBall (0 : E) (3 / 4)
      exact mem_closedBall.mpr (mem_ball.mp hxB).le
    have hxr : ChartDistance.chartParametrization U (fun _ => isOpen_ball)
        (i := 0) (F k ∘ q) x ∈ range (e k) := by
      have heval : ChartDistance.chartParametrization U (fun _ => isOpen_ball)
          (i := 0) (F k ∘ q) x = F k (q xp) :=
        ChartDistance.chartParametrization_apply U (fun _ => isOpen_ball)
          (i := 0) (F k ∘ q) xp
      rw [heval]
      exact hr xp hxpC
    have hread : ContDiffAt ℝ ∞
        (fun y : E => (Function.invFun (e k)
          (ChartDistance.chartParametrization U (fun _ => isOpen_ball)
            (i := 0) (F k ∘ q) y)).val) x :=
      ChartDistance.contDiffAt_source_readout (n := n) U (fun _ => isOpen_ball)
        (M := M k) (i := 0) (e := e k)
        (hsmooth k) (hopen k).injective (hopen k).isOpen_range
        (f := ChartDistance.chartParametrization U (fun _ => isOpen_ball)
          (i := 0) (F k ∘ q)) (x := x)
        (hk.contMDiffAt (closedBall_mem_nhds_of_mem hxB)) hxr
    change DifferentiableAt ℝ
      (fun y : E => (Function.invFun (e k)
        (ChartDistance.chartParametrization U (fun _ => isOpen_ball)
          (i := 0) (F k ∘ q) y)).val) x
    exact hread.differentiableAt (by simp)
  have hvalue : TendstoUniformlyOn a id atTop (closedBall (0 : E) (1 / 2)) := by
    have hj : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (a k))
        (iteratedFDeriv ℝ 0 id) atTop (closedBall (0 : E) (1 / 2)) := hjet 0
    have hv := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → E)).comp_tendstoUniformlyOn hj
    change TendstoUniformlyOn a id atTop (closedBall (0 : E) (1 / 2)) at hv
    exact hv
  have hzero : Tendsto (fun k => a k 0) atTop (𝓝 (0 : E)) := by
    simpa only [id_eq] using hvalue.tendsto_at (by simp)
  have hderiv : TendstoUniformlyOn (fun k x => fderiv ℝ (a k) x)
      (fun _ => ContinuousLinearMap.id ℝ E) atTop (closedBall 0 (1 / 2)) := by
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply, fderiv_id] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → E)).comp_tendstoUniformlyOn
          (tendstoUniformlyOn_fderiv_jets 0 (hjet 1))
  have hdiff' : ∀ᶠ k in atTop, ∀ x ∈ closedBall (0 : E) (2 / 4),
      DifferentiableAt ℝ (a k) x := by convert hdiff using 1; norm_num
  have hderiv' : TendstoUniformlyOn (fun k x => fderiv ℝ (a k) x)
      (fun _ => ContinuousLinearMap.id ℝ E) atTop (closedBall 0 (2 / 4)) := by
    convert hderiv using 1
    norm_num
  have hcore : ∀ᶠ k in atTop, closedBall (0 : E) (1 / 4) ⊆
      a k '' closedBall 0 (1 / 2) := by
    convert eventually_coordinate_core_subset_image a (ρ := 2) (by norm_num)
      hdiff' hzero hderiv' using 1
    norm_num
  filter_upwards [hcore, hreach] with k hk hr y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨x, hx, hax⟩ := hk hz
  have hxC : x ∈ closedBall (0 : E) (3 / 4) :=
    closedBall_subset_closedBall (by norm_num) hx
  let xp : ball (0 : E) 1 := ⟨x, hCU hxC⟩
  have hxpC : xp ∈ C := by
    change x ∈ closedBall (0 : E) (3 / 4)
    exact hxC
  have hinv : Function.invFun (e k) (F k (q xp)) = z := by
    apply Subtype.ext
    have heval : a k (xp : E) = (Function.invFun (e k) (F k (q xp))).val :=
      ChartDistance.coordinateRepresentative_apply U (fun _ => isOpen_ball)
        (i := 0) (j := 0) (fun y => Function.invFun (e k) (F k (q y))) xp
    exact heval.symm.trans hax
  refine ⟨q xp, hA ⟨xp, hx, rfl⟩, ?_⟩
  have hid := Function.invFun_eq (hr xp hxpC)
  rw [hinv] at hid
  exact hid.symm



theorem eventually_source_core_subset_exhaustion_image
    {n : ℕ} [Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1)]
    (O : OverlapSystem (fun _ : ℕ => ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hO : SmoothOverlap (fun _ : ℕ => ball 0 1) (fun _ => isOpen_ball) O)
    {V : ℕ → Set (Quotient O.setoid)}
    (hV : ∀ k, IsOpen (V k)) (hVmono : Monotone V) (hVcover : (⋃ k, V k) = univ)
    {M : ℕ → Type u} [∀ k, MetricSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    (F : ∀ k, Quotient O.setoid → M k)
    (hF :
      letI := quotientChartedSpace (fun _ : ℕ => ball 0 1) (fun _ => isOpen_ball) O
      ∀ k, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (F k) (V k))
    (e : ∀ k, ball (0 : EuclideanSpace ℝ (Fin n)) 1 → M k)
    {i : ℕ} {L : ℝ≥0} (he : ∀ k, LipschitzWith L (e k))
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ k x y, c * dist x y ≤ dist (e k x) (e k y))
    (hopen : ∀ k, Topology.IsOpenEmbedding (e k))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))
    (hsmooth :
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n))
          (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (happrox : ∀ C, IsCompact C → TendstoUniformlyOn
      (fun k x => dist (F k (O.include i x)) (e k x)) (fun _ => 0) atTop C)
    (hjet : ∀ m K, IsCompact K → K ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
        (ChartDistance.coordinateRepresentative (fun _ : ℕ => ball 0 1)
          (fun _ => isOpen_ball) (i := i) (j := i)
            (fun x => Function.invFun (e k) (F k (O.include i x)))))
        (iteratedFDeriv ℝ m id) atTop K)
    (j : ℕ)
    (hbuffer : O.include i '' {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
      x.val ∈ closedBall 0 (1 / 2)} ⊆ V j) :
    ∀ᶠ k in atTop, e k '' {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
      x.val ∈ closedBall 0 (1 / 4)} ⊆ F k '' V j := by
  apply eventually_source_core_subset_image e (O.include i) F he hc hlower hopen
    hconn hsmooth happrox ?_ ?_ (V j) hbuffer
  · exact ChartDistance.eventually_contMDiffOn_source_exhaustion_chart
      (fun _ : ℕ => ball 0 1) (fun _ => isOpen_ball) O hO hV hVmono hVcover F hF i
      (isCompact_closedBall 0 (3 / 4)) (closedBall_subset_ball (by norm_num))
  · intro m
    exact hjet m _ (isCompact_closedBall 0 (1 / 2))
      (closedBall_subset_ball (by norm_num))

end PoincareConjecture.M28
