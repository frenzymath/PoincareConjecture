import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessHolder
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessModulus



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

private theorem unscale_jets {d : ℕ}
    (F : ℕ → LoopPlane → EuclideanSpace ℝ (Fin d)) (a : LoopPlane)
    {t : ℝ} (ht : 0 < t)
    (heq : EquicontinuousAt (fun j z =>
      (F j (a + t • z), fderiv ℝ (fun y => F j (a + t • y)) z)) 0) :
    EquicontinuousAt (fun j z => (F j z, fderiv ℝ (F j) z)) a := by
  let B := max 1 t⁻¹
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let q := fun x : LoopPlane => t⁻¹ • (x - a)
  have hq : Tendsto q (𝓝 a) (𝓝 0) := by
    have hc : Continuous q := by dsimp only [q]; fun_prop
    simpa only [q, sub_self, smul_zero] using hc.tendsto a
  apply Metric.equicontinuousAt_iff_right.mpr
  intro epsilon hepsilon
  filter_upwards [hq.eventually (Metric.equicontinuousAt_iff_right.mp heq
    (epsilon / B) (div_pos hepsilon hB))] with x hx
  intro j
  have hid : a + t • q x = x := by dsimp only [q]; simp [smul_smul, ht.ne']
  have h := hx j
  simp only [smul_zero, add_zero, suRescale_fderiv, hid, Prod.dist_eq] at h
  have hv : dist (F j a) (F j x) < epsilon / B := (max_lt_iff.mp h).1
  have hd : dist (t • fderiv ℝ (F j) a) (t • fderiv ℝ (F j) x) < epsilon / B :=
    (max_lt_iff.mp h).2
  have hv' : dist (F j a) (F j x) < epsilon := by
    have hEB : epsilon / B ≤ epsilon := (div_le_self hepsilon.le (le_max_left _ _))
    exact hv.trans_le hEB
  have hd' : dist (fderiv ℝ (F j) a) (fderiv ℝ (F j) x) < epsilon := by
    have he : dist (fderiv ℝ (F j) a) (fderiv ℝ (F j) x) =
        t⁻¹ * dist (t • fderiv ℝ (F j) a) (t • fderiv ℝ (F j) x) := by
      rw [dist_eq_norm, dist_eq_norm,
        ← smul_sub t (fderiv ℝ (F j) a) (fderiv ℝ (F j) x),
        norm_smul, Real.norm_of_nonneg ht.le]
      field_simp
    rw [he]
    calc
      _ ≤ B * dist (t • fderiv ℝ (F j) a) (t • fderiv ℝ (F j) x) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
      _ < B * (epsilon / B) := mul_lt_mul_of_pos_left hd hB
      _ = epsilon := by field_simp
  exact max_lt hv' hd'

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

set_option maxHeartbeats 3200000 in




theorem suNormalized_firstJets_equicontinuous
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
      (fun y => e (f j ((chartAt LoopPlane (center j)).symm (scale j • y)))) z‖ ≤ C) :
    let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
    Equicontinuous (fun j z => (e (v j z), fderiv ℝ (e ∘ v j) z)) := by
  let v := fun j z => f j ((chartAt LoopPlane (center j)).symm (scale j • z))
  have hv (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (v j) :=
    (hf j).comp ((suSphereChart_smooth (center j)).comp
      (contDiff_id.const_smul (scale j)).contMDiff)
  change Equicontinuous (fun j z => (e (v j z), fderiv ℝ (e ∘ v j) z))
  intro a
  obtain ⟨p, L, r, t, N, A, F, hr, ht, hA, hF, hKt, hchart, hU, hjet, hsource, hres⟩ :=
    suNormalized_local_equations g e he hread alpha f hf ha har heq center scale hs
      v0 hC hlim hgrad a
  let K := Metric.closedBall ((extChartAt (𝓡 n) p) (v0 a)) r
  let U := fun j z => L (e (v (j + N) (a + t • z)))
  let lambda := fun j z => suAlphaRoundFactor (scale (j + N) • (a + t • z))
  let rho := fun j => scale (j + N) * t
  let c := fun j => alpha (j + N) - 1
  let source := fun j => suNormalizedAlphaCoordinateSource g p (U j) (lambda j) (rho j) (c j)
  have himage (z : LoopPlane) (hz : z ∈ Metric.closedBall (0 : LoopPlane) 2) :
      a + t • z ∈ Metric.closedBall a (4 * t) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.le]
    have hzn : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  have htarget (j : ℕ) : MapsTo (U j) (Metric.ball (0 : LoopPlane) 2) K := by
    intro z hz
    have h := hchart j (a + t • z) (himage z (Metric.ball_subset_closedBall hz))
    change L (e (v (j + N) (a + t • z))) ∈ K
    have hx : L (e (v (j + N) (a + t • z))) =
        (extChartAt (𝓡 n) p) (v (j + N) (a + t • z)) := h.2.2.self_of_nhds
    rw [hx]
    exact h.2.1
  have hsc (j : ℕ) : ContinuousOn (source j) (Metric.ball (0 : LoopPlane) 2) := by
    apply suNormalizedAlphaCoordinateSource_continuousOn g p (U j) (lambda j) Metric.isOpen_ball
      (isCompact_closedBall _ _) hKt (hU j)
      (suRoundFactor_smooth_pos.1.comp
        ((contDiff_const.add (contDiff_id.const_smul t)).const_smul (scale (j + N))))
      (htarget j) (fun x _ => suRoundFactor_smooth_pos.2 _)
      (mul_pos (hs (j + N)).1 ht)
  obtain ⟨delta, B, hdelta, hB, hmod⟩ := suSmooth_nearLaplacian_gradient_modulus
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hres delta hdelta)
  have hholder (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall (0 : LoopPlane) (1 / 4))
      (i : Fin 2) :
      ‖fderiv ℝ (U (j + N1)) z (b i) - fderiv ℝ (U (j + N1)) 0 (b i)‖ ≤
        (B * (A + F)) * Real.sqrt (Real.sqrt (dist z 0)) :=
    hmod n A F hA hF (U (j + N1)) (source (j + N1)) (hU (j + N1)) (hsc (j + N1))
      (hjet (j + N1)) (hsource (j + N1)) (hN1 (j + N1) (Nat.le_add_left _ _))
      i z hz 0 (Metric.mem_closedBall_self (by norm_num))
  let W := fun j z => v (j + N1 + N) (a + t • z)
  have hW (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (W j) :=
    (hv (j + N1 + N)).comp (contDiff_const.add (contDiff_id.const_smul t)).contMDiff
  have hWgrad (j : ℕ) (z : LoopPlane) : ‖fderiv ℝ (e ∘ W j) z‖ ≤ t * C := by
    change ‖fderiv ℝ (fun y => (e ∘ v (j + N1 + N)) (a + t • y)) z‖ ≤ _
    rw [suRescale_fderiv, norm_smul, Real.norm_of_nonneg ht.le]
    exact mul_le_mul_of_nonneg_left (hgrad _ _) ht.le
  have hWchart (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall (0 : LoopPlane) (1 / 4)) :
      W j z ∈ (extChartAt (𝓡 n) p).source ∧ (extChartAt (𝓡 n) p) (W j z) ∈ K ∧
      (fun q => L (e q)) =ᶠ[𝓝 (W j z)] extChartAt (𝓡 n) p :=
    hchart (j + N1) (a + t • z) (himage z ((Metric.closedBall_subset_closedBall (by norm_num)) hz))
  have hscaled : EquicontinuousAt (fun j z => (e (W j z), fderiv ℝ (e ∘ W j) z)) 0 := by
    apply suObservedJets_equicontinuousAt_of_chart e he W hW p L (isCompact_closedBall _ _)
      hKt 0 (by norm_num : (0 : ℝ) < 1 / 4) (mul_nonneg ht.le hC)
      (mul_nonneg hB.le (add_nonneg hA hF)) hWchart hWgrad
    exact hholder
  have htail : EquicontinuousAt (fun j z =>
      (e (v (j + (N1 + N)) z), fderiv ℝ (e ∘ v (j + (N1 + N))) z)) a := by
    simpa only [Nat.add_assoc, W, Function.comp_def] using
      unscale_jets (fun j => e ∘ v (j + N1 + N)) a ht hscaled
  apply suEquicontinuousAt_of_tail _ a (N1 + N) _ htail
  intro j
  have hc := contMDiff_iff_contDiff.mp (he.comp (hv j))
  exact hc.continuous.continuousAt.prodMk (hc.continuous_fderiv (by simp)).continuousAt

end PoincareConjecture.M60
