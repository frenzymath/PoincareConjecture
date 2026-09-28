import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessDisk
import Mathlib.Topology.MetricSpace.Equicontinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

theorem suEquicontinuousAt_of_tail {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y] (F : ℕ → X → Y) (a : X) (N : ℕ)
    (hF : ∀ j, ContinuousAt (F j) a)
    (htail : EquicontinuousAt (fun j => F (j + N)) a) : EquicontinuousAt F a := by
  have hhead : EquicontinuousAt (fun j : Fin N => F j) a :=
    equicontinuousAt_finite.mpr fun j => hF j
  apply Metric.equicontinuousAt_iff_right.mpr
  intro epsilon hepsilon
  filter_upwards [Metric.equicontinuousAt_iff_right.mp hhead epsilon hepsilon,
    Metric.equicontinuousAt_iff_right.mp htail epsilon hepsilon] with x hx ht
  intro j
  by_cases hj : N ≤ j
  · simpa only [Nat.sub_add_cancel hj] using ht (j - N)
  · exact hx ⟨j, Nat.lt_of_not_ge hj⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

set_option maxHeartbeats 2400000 in

theorem suObservedJets_equicontinuousAt_of_chart
    {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (p : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] E)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 n) p).target)
    (a : LoopPlane) {R C H : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hchart : ∀ j z, z ∈ Metric.closedBall a R →
      f j z ∈ (extChartAt (𝓡 n) p).source ∧ (extChartAt (𝓡 n) p) (f j z) ∈ K ∧
      (fun q => L (e q)) =ᶠ[𝓝 (f j z)] extChartAt (𝓡 n) p)
    (hgrad : ∀ j z, ‖fderiv ℝ (e ∘ f j) z‖ ≤ C)
    (hmod : let u := fun j z => L (e (f j z))
      ∀ j z, z ∈ Metric.closedBall a R → ∀ i : Fin 2,
        ‖fderiv ℝ (u j) z (b i) - fderiv ℝ (u j) a (b i)‖ ≤
          H * Real.sqrt (Real.sqrt (dist z a))) :
    EquicontinuousAt (fun j z => (e (f j z), fderiv ℝ (e ∘ f j) z)) a := by
  let u := fun j z => L (e (f j z))
  let B := ‖L‖ * C
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) hC
  have hu (j : ℕ) : ContDiff ℝ ∞ (u j) :=
    L.contDiff.comp (contMDiff_iff_contDiff.mp (he.comp (hf j)))
  have hdu (j : ℕ) (z : LoopPlane) :
      fderiv ℝ (u j) z = L.comp (fderiv ℝ (e ∘ f j) z) :=
    (L.hasFDerivAt.comp z
      ((contMDiff_iff_contDiff.mp (he.comp (hf j))).differentiable (by simp) z).hasFDerivAt).fderiv
  have hdub (j : ℕ) (z : LoopPlane) : ‖fderiv ℝ (u j) z‖ ≤ B := by
    rw [hdu]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (hgrad j z) (norm_nonneg _))
  have hLip (j : ℕ) : LipschitzWith ⟨B, hB⟩ (u j) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hu j).differentiable (by simp)) (hdub j)
  have hderiv (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) :
      ‖fderiv ℝ (u j) z - fderiv ℝ (u j) a‖ ≤
        2 * H * Real.sqrt (Real.sqrt (dist z a)) := by
    let T := fderiv ℝ (u j) z - fderiv ℝ (u j) a
    let q := Real.sqrt (Real.sqrt (dist z a))
    have hq : 0 ≤ q := Real.sqrt_nonneg _
    have hcol (i : Fin 2) : ‖T (b i)‖ ≤ H * q := hmod j z hz i
    have h0 := (sq_le_sq₀ (norm_nonneg (T (b 0))) (mul_nonneg hH hq)).mpr (hcol 0)
    have h1 := (sq_le_sq₀ (norm_nonneg (T (b 1))) (mul_nonneg hH hq)).mpr (hcol 1)
    have hsq := plane_opNorm_sq_le T
    have hpos : 0 ≤ 2 * H * q := by positivity
    nlinarith [norm_nonneg T]
  let J := fun j z => (u j z, fderiv ℝ (u j) z)
  have hJ : EquicontinuousAt J a := by
    let w := fun z => B * dist z a + 2 * H * Real.sqrt (Real.sqrt (dist z a))
    have hw : Continuous w := by dsimp only [w]; fun_prop
    have hwt : Tendsto w (𝓝 a) (𝓝 0) := by
      simpa only [w, dist_self, Real.sqrt_zero, mul_zero, add_zero] using hw.tendsto a
    apply Metric.equicontinuousAt_of_continuity_modulus w hwt J
    filter_upwards [Metric.closedBall_mem_nhds a hR] with z hz
    intro j
    have hv := (hLip j).dist_le_mul a z
    have hd : dist (fderiv ℝ (u j) a) (fderiv ℝ (u j) z) ≤
        2 * H * Real.sqrt (Real.sqrt (dist z a)) := by
      rw [dist_eq_norm, norm_sub_rev]
      exact hderiv j z hz
    change max (dist (u j a) (u j z))
      (dist (fderiv ℝ (u j) a) (fderiv ℝ (u j) z)) ≤ w z
    dsimp only [w]
    rw [dist_comm a z] at hv
    exact max_le (hv.trans (le_add_of_nonneg_right (by positivity)))
      (hd.trans (le_add_of_nonneg_left (mul_nonneg hB (dist_nonneg : 0 ≤ dist z a))))
  let F := e ∘ (extChartAt (𝓡 n) p).symm
  have hF (y : E) (hy : y ∈ K) : ContDiffAt ℝ ∞ F y := by
    have hc := (contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (hKt hy))
    exact contMDiffAt_iff_contDiffAt.mp ((he _).comp y hc)
  let S := K ×ˢ Metric.closedBall (0 : LoopPlane →L[ℝ] E) B
  let Phi := fun q : E × (LoopPlane →L[ℝ] E) => (F q.1, (fderiv ℝ F q.1).comp q.2)
  have hPhi : ContinuousOn Phi S := by
    intro q hq
    have hv : ContinuousAt (fun q : E × (LoopPlane →L[ℝ] E) => F q.1) q :=
      (hF q.1 hq.1).continuousAt.comp_of_eq continuousAt_fst rfl
    have hd : ContinuousAt (fun q : E × (LoopPlane →L[ℝ] E) => fderiv ℝ F q.1) q :=
      ((hF q.1 hq.1).fderiv_right (m := ∞) (by simp)).continuousAt.comp_of_eq
        continuousAt_fst rfl
    exact (hv.prodMk (hd.clm_comp continuousAt_snd)).continuousWithinAt
  have hPhiUC : UniformContinuousOn Phi S :=
    (hK.prod (isCompact_closedBall _ _)).uniformContinuousOn_of_continuous hPhi
  have hJrange (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) : J j z ∈ S := by
    have hh := hchart j z hz
    have heq : L (e (f j z)) = (extChartAt (𝓡 n) p) (f j z) := hh.2.2.self_of_nhds
    refine ⟨?_, ?_⟩
    · change L (e (f j z)) ∈ K
      rw [heq]
      exact hh.2.1
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hdub j z
  have hPhiJ (j : ℕ) (z : LoopPlane) (hz : z ∈ Metric.closedBall a R) :
      Phi (J j z) = (e (f j z), fderiv ℝ (e ∘ f j) z) := by
    have hh := hchart j z hz
    have hg : F ∘ u j =ᶠ[𝓝 z] e ∘ f j := by
      filter_upwards [hh.2.2.comp_tendsto (hf j).continuous.continuousAt,
        (hf j).continuous.continuousAt ((isOpen_extChartAt_source p).mem_nhds hh.1)]
        with x hx hxs
      change e ((extChartAt (𝓡 n) p).symm (L (e (f j x)))) = e (f j x)
      change L (e (f j x)) = (extChartAt (𝓡 n) p) (f j x) at hx
      rw [hx, (extChartAt (𝓡 n) p).left_inv hxs]
    apply Prod.ext
    · exact hg.self_of_nhds
    · have hd := hg.fderiv_eq (𝕜 := ℝ)
      rw [fderiv_comp z ((hF _ (hJrange j z hz).1).differentiableAt (by simp))
        ((hu j).differentiable (by simp) z)] at hd
      exact hd
  apply Metric.equicontinuousAt_iff_right.mpr
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdelta'⟩ := Metric.uniformContinuousOn_iff.mp hPhiUC epsilon hepsilon
  filter_upwards [Metric.closedBall_mem_nhds a hR,
    Metric.equicontinuousAt_iff_right.mp hJ delta hdelta] with z hz hJz
  intro j
  have haR : a ∈ Metric.closedBall a R := Metric.mem_closedBall_self hR.le
  have hh := hdelta' (J j a) (hJrange j a haR) (J j z) (hJrange j z hz) (hJz j)
  rwa [hPhiJ j a haR, hPhiJ j z hz] at hh

end PoincareConjecture.M60
