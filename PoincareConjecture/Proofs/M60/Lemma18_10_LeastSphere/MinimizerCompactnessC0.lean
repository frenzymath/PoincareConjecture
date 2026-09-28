import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessTarget
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import Mathlib.Topology.MetricSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suNormalized_C0_subsequence [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hei : IsClosedEmbedding e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (henergy : ∀ j z, m60EnergyDensity g (f j) z ≤ 1 / 2) :
    ∃ (v : C(LoopPlane, M)) (k : ℕ → ℕ) (C : NNReal), StrictMono k ∧
      (∀ j, LipschitzWith C (e ∘ f j)) ∧
      (∀ j z, ‖fderiv ℝ (e ∘ f j) z‖ ≤ C) ∧
      Tendsto (fun j => (⟨f (k j), (hf (k j)).continuous⟩ : C(LoopPlane, M)))
        atTop (𝓝 v) ∧
      TendstoLocallyUniformly (fun j => e ∘ f (k j)) (e ∘ v) atTop := by
  obtain ⟨B, hB, hd⟩ := exists_observed_derivative_energy_bound g e (he.of_le (by simp))
  let C : NNReal := ⟨Real.sqrt (2 * B), Real.sqrt_nonneg _⟩
  have hfd (j : ℕ) (z : LoopPlane) : ‖fderiv ℝ (e ∘ f j) z‖ ≤ C := by
    have h0 := hd (f j) ((hf j).of_le (by simp)) z 0
    have h1 := hd (f j) ((hf j).of_le (by simp)) z 1
    have hop := plane_opNorm_sq_le (fderiv ℝ (e ∘ f j) z)
    have hnorm := norm_nonneg (fderiv ℝ (e ∘ f j) z)
    have hsqrt : (C : ℝ) ^ 2 = 2 * B := Real.sq_sqrt (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left (henergy j z) hB, C.coe_nonneg]
  have hfc (j : ℕ) : ContDiff ℝ ∞ (e ∘ f j) := contMDiff_iff_contDiff.mp (he.comp (hf j))
  have hLip (j : ℕ) : LipschitzWith C (e ∘ f j) :=
    lipschitzWith_of_nnnorm_fderiv_le ((hfc j).differentiable (by simp)) (hfd j)
  have hequi : Equicontinuous (fun j => e ∘ f j) :=
    (LipschitzWith.uniformEquicontinuous _ C hLip).equicontinuous
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn he.continuous.continuousOn
  let : T2Space (UniformOnFun LoopPlane (EuclideanSpace ℝ (Fin d)) {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩)
  let J : ℕ → C(LoopPlane, EuclideanSpace ℝ (Fin d)) := fun j =>
    ⟨e ∘ f j, (hfc j).continuous⟩
  have hequi' : Equicontinuous (fun v : range J => (v.1 : LoopPlane → _)) := by
    have hJ : (fun v : range J => (fun z => J v.2.choose z)) =
        (fun v : range J => (v.1 : LoopPlane → _)) := by
      funext v z
      exact congrArg (fun w : C(LoopPlane, EuclideanSpace ℝ (Fin d)) => w z) v.2.choose_spec
    rw [← hJ]
    exact hequi.comp fun v : range J => v.2.choose
  have hc : IsCompact (closure (range J)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := ContinuousMap.toFun) (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K _ => hequi'.equicontinuousOn K) (by
        intro K _ z _
        refine ⟨Metric.closedBall 0 A, isCompact_closedBall _ _, ?_⟩
        rintro _ ⟨j, rfl⟩
        simpa only [mem_closedBall_zero_iff, J, ContinuousMap.coe_mk,
          Function.comp_apply] using hA (f j z) (mem_univ _))
  obtain ⟨u, _, k, hk, hlim⟩ := hc.tendsto_subseq
    (fun j => subset_closure (mem_range_self j))
  have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  have hrange (z) : u z ∈ range e := hei.isClosed_range.mem_of_tendsto
    (ht.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
    (Eventually.of_forall fun j => mem_range_self (f (k j) z))
  let v : LoopPlane → M := fun z => hei.isEmbedding.toHomeomorph.symm ⟨u z, hrange z⟩
  have hev : e ∘ v = u := by
    funext z
    exact congrArg Subtype.val (hei.isEmbedding.toHomeomorph.apply_symm_apply ⟨u z, hrange z⟩)
  have hv : Continuous v := hei.isEmbedding.continuous_iff.mpr (hev ▸ u.continuous)
  refine ⟨⟨v, hv⟩, k, C, hk, hLip, hfd, ?_, ?_⟩
  · apply (ContinuousMap.isEmbedding_postcomp
      (⟨e, he.continuous⟩ : C(M, EuclideanSpace ℝ (Fin d))) hei.isEmbedding).tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
    change TendstoLocallyUniformly (fun j => e ∘ f (k j)) (e ∘ v) atTop
    simpa only [hev, J, ContinuousMap.coe_mk, Function.comp_apply] using! ht
  · simpa only [ContinuousMap.coe_mk, hev, J, Function.comp_apply] using! ht

omit [IsManifold (𝓡 n) ∞ M] in

theorem suC0_common_readable_chart
    {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d)) (hread : SUChartReadable (n := n) e)
    (f : ℕ → C(LoopPlane, M)) (f0 : C(LoopPlane, M))
    (hlim : Tendsto f atTop (𝓝 f0)) (a : LoopPlane) :
    ∃ (b : M) (L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n)) (r R : ℝ),
      0 < r ∧ 0 < R ∧
      Metric.closedBall ((extChartAt (𝓡 n) b) (f0 a)) r ⊆ (extChartAt (𝓡 n) b).target ∧
      (∀ z ∈ Metric.closedBall a R,
        f0 z ∈ (extChartAt (𝓡 n) b).source ∧
        (extChartAt (𝓡 n) b) (f0 z) ∈ Metric.ball ((extChartAt (𝓡 n) b) (f0 a)) r ∧
        (fun q => L (e q)) =ᶠ[𝓝 (f0 z)] (extChartAt (𝓡 n) b)) ∧
      ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall a R,
        f j z ∈ (extChartAt (𝓡 n) b).source ∧
        (extChartAt (𝓡 n) b) (f j z) ∈ Metric.ball ((extChartAt (𝓡 n) b) (f0 a)) r ∧
        (fun q => L (e q)) =ᶠ[𝓝 (f j z)] (extChartAt (𝓡 n) b) := by
  obtain ⟨b, hb, L, hL⟩ := hread (f0 a)
  let c := extChartAt (𝓡 n) b
  let W := interior {q : M | L (e q) = c q} ∩ c.source
  have hW : IsOpen W := isOpen_interior.inter (isOpen_extChartAt_source b)
  have hbW : f0 a ∈ W := ⟨mem_interior_iff_mem_nhds.mpr hL, hb⟩
  have hcb : c (f0 a) ∈ c.target := c.map_source hb
  have hnear : ∀ᶠ y in 𝓝 (c (f0 a)), y ∈ c.target ∧ c.symm y ∈ W := by
    have hcs : ContinuousAt c.symm (c (f0 a)) :=
      (continuousOn_extChartAt_symm b).continuousAt ((isOpen_extChartAt_target b).mem_nhds hcb)
    have hx : c.symm (c (f0 a)) ∈ W := by rwa [c.left_inv hb]
    filter_upwards [(isOpen_extChartAt_target b).mem_nhds hcb,
      hcs.preimage_mem_nhds (hW.mem_nhds hx)] with y hy hyW
    exact ⟨hy, hyW⟩
  obtain ⟨s, hs, hsB⟩ := Metric.mem_nhds_iff.mp hnear
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hball (y : EuclideanSpace ℝ (Fin n))
      (hy : y ∈ Metric.closedBall (c (f0 a)) r) : y ∈ c.target ∧ c.symm y ∈ W :=
    hsB ((Metric.mem_closedBall.mp hy).trans_lt (by dsimp [r]; linarith))
  let V := c.source ∩ c ⁻¹' Metric.ball (c (f0 a)) r
  have hV : IsOpen V := (continuousOn_extChartAt b).isOpen_inter_preimage
    (isOpen_extChartAt_source b) Metric.isOpen_ball
  have hbV : f0 a ∈ V := ⟨hb, Metric.mem_ball_self hr⟩
  have hgood {x : M} (hx : x ∈ V) : x ∈ c.source ∧
      c x ∈ Metric.ball (c (f0 a)) r ∧ (fun q => L (e q)) =ᶠ[𝓝 x] c := by
    have hxW : x ∈ W := by
      have h := (hball (c x) (Metric.ball_subset_closedBall hx.2)).2
      rwa [c.left_inv hx.1] at h
    refine ⟨hx.1, hx.2, ?_⟩
    filter_upwards [isOpen_interior.mem_nhds hxW.1] with y hy
    exact interior_subset (s := {q : M | L (e q) = c q}) hy
  have hsource : ∀ᶠ z in 𝓝 a, f0 z ∈ V :=
    f0.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hbV)
  obtain ⟨S, hS, hSB⟩ := Metric.mem_nhds_iff.mp hsource
  let R := S / 2
  have hR : 0 < R := half_pos hS
  have hlocal : MapsTo f0 (Metric.closedBall a R) V := by
    intro z hz
    exact hSB ((Metric.mem_closedBall.mp hz).trans_lt (by dsimp [R]; linarith))
  have htail : ∀ᶠ j in atTop, MapsTo (f j) (Metric.closedBall a R) V :=
    hlim (ContinuousMap.eventually_mapsTo (isCompact_closedBall _ _) hV hlocal)
  refine ⟨b, L, r, R, hr, hR, fun y hy => (hball y hy).1,
    fun z hz => hgood (hlocal hz), ?_⟩
  exact htail.mono fun j hj z hz => hgood (hj hz)

end PoincareConjecture.M60
