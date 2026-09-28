import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerFields
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLinearChart











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler

private theorem bounded_extension {N K : ℕ}
    {h : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)}
    {a : EuclideanSpace ℝ (Fin N)} (hh : ContDiffAt ℝ 1 h a) :
    ∃ (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K)) (C : NNReal),
      ContDiff ℝ 1 g ∧ (∀ y, ‖fderiv ℝ g y‖ ≤ (C : ℝ)) ∧ g =ᶠ[𝓝 a] h := by
  obtain ⟨r, hr, hrc⟩ := Metric.mem_nhds_iff.mp (hh.eventually (by simp))
  let χ : ContDiffBump a :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g (y : EuclideanSpace ℝ (Fin N)) := χ y • h y
  have hg : ContDiff ℝ 1 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ ball a r
    · exact χ.contDiff.contDiffAt.smul (hrc hy)
    · have hys : y ∉ tsupport χ := by
        rw [χ.tsupport_eq]
        exact fun h => hy ((closedBall_subset_ball (by dsimp only [χ]; linarith)) h)
      have hz : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
        change χ z • h z = 0
        simp only [hz, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  obtain ⟨C, hC⟩ := (hgc.fderiv ℝ).exists_bound_of_continuous (hg.continuous_fderiv one_ne_zero)
  refine ⟨g, ⟨max C 0, le_max_right _ _⟩, hg, fun y => (hC y).trans (le_max_left _ _), ?_⟩
  filter_upwards [χ.eventuallyEq_one] with y hy
  change χ y • h y = h y
  simp only [hy, Pi.one_apply, one_smul]

private theorem chart_extensions {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M) :
    ∃ (H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 3))
      (B : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin N)) (CH CB : NNReal),
      ContDiff ℝ 1 H ∧ ContDiff ℝ 1 B ∧
      (∀ y, ‖fderiv ℝ H y‖ ≤ (CH : ℝ)) ∧
      (∀ y, ‖fderiv ℝ B y‖ ≤ (CB : ℝ)) ∧
      ∀ᶠ q in 𝓝 p,
        q ∈ (extChartAt (𝓡 3) p).source ∧
        H (e q) = extChartAt (𝓡 3) p q ∧
        B (extChartAt (𝓡 3) p q) = e q ∧
        fderiv ℝ B (extChartAt (𝓡 3) p q) =
          fderiv ℝ (e ∘ (extChartAt (𝓡 3) p).symm) (extChartAt (𝓡 3) p q) := by
  let c := extChartAt (𝓡 3) p
  obtain ⟨L, P, hP0, hP, hPinv⟩ := m65Embedding_exists_linear_chart e he hinj p
  have hcP : ContDiffAt ℝ ∞ (fun y => c (P y)) 0 := by
    have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c (P 0) :=
      hP0.symm ▸ (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞))
    exact contMDiffAt_iff_contDiffAt.mp (hc.comp 0 hP)
  have hlin : ContDiffAt ℝ ∞ (fun y => L (y - e p)) (e p) :=
    L.contDiff.contDiffAt.comp (e p) (contDiffAt_id.sub contDiffAt_const)
  have hh : ContDiffAt ℝ 1 (fun y => c (P (L (y - e p)))) (e p) := by
    have hcp' : ContDiffAt ℝ ∞ (fun y => c (P y)) (L (e p - e p)) := by
      simpa only [sub_self, map_zero] using hcP
    have hfull : ContDiffAt ℝ ∞ (fun y => c (P (L (y - e p)))) (e p) :=
      ContDiffAt.comp (f := fun y => L (y - e p)) (g := fun y => c (P y)) (e p) hcp' hlin
    exact hfull.of_le (by simp)
  obtain ⟨H, CH, hH, hHb, hHeq⟩ := bounded_extension hh
  have hcsi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (c p) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p (mem_extChartAt_target p)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target p))
  have hb : ContDiffAt ℝ 1 (e ∘ c.symm) (c p) :=
    (contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt.comp (c p) hcsi)).of_le (by simp)
  obtain ⟨B, CB, hB, hBb, hBeq⟩ := bounded_extension hb
  refine ⟨H, B, CH, CB, hH, hB, hHb, hBb, ?_⟩
  have hce : ContinuousAt c p := (contMDiffAt_extChartAt (I := 𝓡 3) (n := ∞)).continuousAt
  filter_upwards [he.continuous.continuousAt.eventually hHeq, hPinv,
    hce.eventually hBeq.eventually_nhds,
    (isOpen_extChartAt_source (I := 𝓡 3) p).mem_nhds (mem_extChartAt_source p)]
    with q hHq hPq hBq hqs
  change B =ᶠ[𝓝 (c q)] e ∘ c.symm at hBq
  refine ⟨hqs, ?_, ?_, hBq.fderiv_eq⟩
  · rw [hHq, hPq]
  · rw [hBq.eq_of_nhds]
    exact congrArg e (c.left_inv hqs)

set_option maxHeartbeats 1600000 in






theorem exists_chart_graph {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    {S : Set LoopPlane} (hS : IsOpen S) (F : M65LocalWeakMap e S)
    (q : LoopPlane → M) (hc : ContinuousOn q S)
    (hq : q =ᵐ[volume.restrict S] F.value) {x : LoopPlane} (hx : x ∈ S) :
    ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ S ∧
      ∃ G : M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin 3) => y) (ball x R),
        (∀ z, G.value z = extChartAt (𝓡 3) (q x) (q z)) ∧
        (∀ z ∈ ball x R, q z ∈ (extChartAt (𝓡 3) (q x)).source) ∧
        ∀ i, F.derivative i =ᵐ[volume.restrict (ball x R)] fun z =>
          fderiv ℝ (e ∘ (extChartAt (𝓡 3) (q x)).symm)
            (extChartAt (𝓡 3) (q x) (q z)) (G.derivative i z) := by
  let c := extChartAt (𝓡 3) (q x)
  obtain ⟨H, B, CH, CB, hH, hB, hHb, hBb, hcap⟩ := chart_extensions e he hinj (q x)
  have hqc : ContinuousAt q x := hc.continuousAt (hS.mem_nhds hx)
  obtain ⟨η, hη, hηcap⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hS.mem_nhds hx) (hqc.eventually hcap))
  let R := η / 4
  have hR : 0 < R := by dsimp only [R]; positivity
  have h2η : 2 * R < η := by dsimp only [R]; linarith
  have h2S : closedBall x (2 * R) ⊆ S :=
    fun z hz => (hηcap ((closedBall_subset_ball h2η) hz)).1
  have h2cap (z : LoopPlane) (hz : z ∈ closedBall x (2 * R)) :
      q z ∈ c.source ∧ H (e (q z)) = c (q z) ∧ B (c (q z)) = e (q z) ∧
        fderiv ℝ B (c (q z)) = fderiv ℝ (e ∘ c.symm) (c (q z)) :=
    (hηcap ((closedBall_subset_ball h2η) hz)).2
  have hR2 : closedBall x R ⊆ ball x (2 * R) :=
    closedBall_subset_ball (by linarith)
  have hbR2 : ball x R ⊆ ball x (2 * R) := ball_subset_closedBall.trans hR2
  have hRS : closedBall x R ⊆ S := hR2.trans (ball_subset_closedBall.trans h2S)
  have hqe : (fun z => e (q z)) =ᵐ[volume.restrict S] fun z => e (F.value z) :=
    hq.mono (fun _ hz => congrArg e hz)
  let Fq := replace_value F q hqe
  let G0 := compose_on_ball Fq hS x (by linarith : 0 ≤ 2 * R) h2S H hH CH hHb
  have hG0 : (fun z => c (q z)) =ᵐ[volume.restrict (ball x (2 * R))] G0.value := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (h2cap z (ball_subset_closedBall hz)).2.1.symm
  let G := replace_value G0 (fun z => c (q z)) hG0
  let back := compose_on_ball G isOpen_ball x hR.le hR2 B hB CB hBb
  let Fsmall := restrict_map F (ball_subset_closedBall.trans hRS)
  have hback : (fun z => e (Fsmall.value z)) =ᵐ[volume.restrict (ball x R)] back.value := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hRS) hqe,
      ae_restrict_mem measurableSet_ball] with z hz hzs
    change e (F.value z) = B (c (q z))
    rw [(h2cap z (ball_subset_closedBall (hbR2 hzs))).2.2.1, hz]
  refine ⟨R, hR, hRS, restrict_map G hbR2, fun _ => rfl, ?_, ?_⟩
  · intro z hz
    exact (h2cap z (ball_subset_closedBall (hbR2 hz))).1
  · intro i
    have hd := derivative_unique isOpen_ball Fsmall back hback i
    filter_upwards [hd, ae_restrict_mem measurableSet_ball] with z hz hzs
    change F.derivative i z = fderiv ℝ (e ∘ c.symm) (c (q z)) (G.derivative i z)
    change F.derivative i z = fderiv ℝ B (c (q z)) (G.derivative i z) at hz
    rw [hz, (h2cap z (ball_subset_closedBall (hbR2 hzs))).2.2.2]

end PoincareConjecture.M65Euler
