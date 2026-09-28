import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationInverse
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFamily
import PoincareConjecture.Proofs.M09.ChartVelocity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

private theorem scalar_angular_neighborhood
    (h : ((ℝ × P) × ℝ) → ℝ) (w : (ℝ × P) × ℝ)
    (hh : ContDiffAt ℝ 1 h w) (hne : fderiv ℝ h w ((1, 0), 0) ≠ 0) :
    ∃ W : Set ((ℝ × P) × ℝ), IsOpen W ∧ w ∈ W ∧
      (∀ z ∈ W, fderiv ℝ h z ((1, 0), 0) ≠ 0) ∧
      ∀ p t, InjOn (fun x => h ((x, p), t)) {x | ((x, p), t) ∈ W} := by
  have hlinear (x : ℝ) : fderiv ℝ h w ((x, 0), 0) =
      x * fderiv ℝ h w ((1, 0), 0) := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, smul_zero] using
      (fderiv ℝ h w).map_smul x ((1, 0), 0)
  have hblock : Function.Bijective (fun x : ℝ => fderiv ℝ h w ((x, 0), 0)) := by
    constructor
    · intro x y hxy
      change fderiv ℝ h w ((x, 0), 0) = fderiv ℝ h w ((y, 0), 0) at hxy
      rw [hlinear x, hlinear y] at hxy
      exact mul_right_cancel₀ hne hxy
    · intro y
      refine ⟨y / fderiv ℝ h w ((1, 0), 0), ?_⟩
      change fderiv ℝ h w ((y / fderiv ℝ h w ((1, 0), 0), 0), 0) = y
      rw [hlinear, div_mul_cancel₀ _ hne]
  obtain ⟨e, hwe, he, _⟩ := exists_augmented_inverse h w hh hblock
  have hc : ContinuousAt (fun z => fderiv ℝ h z ((1, 0), 0)) w :=
    (hh.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  obtain ⟨V, hV, hVo, hwV⟩ := _root_.mem_nhds_iff.mp (hc.eventually_ne hne)
  refine ⟨e.source ∩ V, e.open_source.inter hVo, ⟨hwe, hwV⟩,
    fun z hz => hV hz.2, ?_⟩
  intro p t x hx y hy hxy
  change h ((x, p), t) = h ((y, p), t) at hxy
  have heq : e ((x, p), t) = e ((y, p), t) := by rw [he, he, hxy]
  exact congrArg (fun z : (ℝ × P) × ℝ => z.1.1) (e.injOn hx.1 hy.1 heq)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

omit [CompleteSpace P] in
private theorem chart_angular_derivative
    (c : ((ℝ × P) × ℝ) → M) (w : (ℝ × P) × ℝ) (q : M)
    (hc : ContMDiffAt 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1 c w)
    (hq : c w ∈ (chartAt LoopAmbient q).source) :
    fderiv ℝ (fun z => (chartAt LoopAmbient q) (c z)) w ((1, 0), 0) =
      mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient q) (c w)
        (curveVelocity (n := 3) (fun x => c ((x, w.1.2), w.2)) w.1.1) := by
  have he : ContMDiffAt (𝓡 3) (𝓡 3) 1 (chartAt LoopAmbient q) (c w) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hq
  have hcoord : ContDiffAt ℝ 1 (fun z => (chartAt LoopAmbient q) (c z)) w :=
    (he.comp w hc).contDiffAt
  have hline : HasDerivAt (fun x : ℝ => ((x, w.1.2), w.2)) ((1, 0), 0) w.1.1 :=
    ((hasDerivAt_id w.1.1).prodMk (hasDerivAt_const w.1.1 w.1.2)).prodMk
      (hasDerivAt_const w.1.1 w.2)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3)
      (fun x => c ((x, w.1.2), w.2)) w.1.1 :=
    (hc.comp w.1.1 ((contDiff_id.prodMk contDiff_const).prodMk
      contDiff_const).contMDiff.contMDiffAt).mdifferentiableAt one_ne_zero
  have hfirst : HasDerivAt (fun x => (chartAt LoopAmbient q) (c ((x, w.1.2), w.2)))
      (fderiv ℝ (fun z => (chartAt LoopAmbient q) (c z)) w ((1, 0), 0)) w.1.1 := by
    simpa +instances only [Function.comp_def, Prod.eta] using!
      hcoord.differentiableAt_one.hasFDerivAt.comp_hasDerivAt w.1.1 hline
  simpa +instances only [Prod.eta] using! hfirst.unique
    (Proofs.M09.hasDerivAt_chart_curve q (fun x => c ((x, w.1.2), w.2))
      w.1.1 hq hcurve)

set_option maxHeartbeats 600000 in

theorem exists_angular_neighborhood
    (c : ((ℝ × P) × ℝ) → M) (U : Set ((ℝ × P) × ℝ)) (hU : IsOpen U)
    (hc : ContMDiffOn 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1 c U)
    (w : (ℝ × P) × ℝ) (hw : w ∈ U)
    (hv : curveVelocity (n := 3) (fun x => c ((x, w.1.2), w.2)) w.1.1 ≠ 0) :
    ∃ W : Set ((ℝ × P) × ℝ), IsOpen W ∧ w ∈ W ∧ W ⊆ U ∧
      (∀ z ∈ W,
        curveVelocity (n := 3) (fun x => c ((x, z.1.2), z.2)) z.1.1 ≠ 0) ∧
      ∀ p t, InjOn (fun x => c ((x, p), t)) {x | ((x, p), t) ∈ W} := by
  let q := c w
  let e := chartAt LoopAmbient q
  let H : ((ℝ × P) × ℝ) → LoopAmbient := fun z => e (c z)
  have hwq : c w ∈ e.source := mem_chart_source _ _
  have hcw := hc.contMDiffAt (hU.mem_nhds hw)
  have hchart : ContMDiffAt (𝓡 3) (𝓡 3) 1 e (c w) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hwq
  have hH : ContDiffAt ℝ 1 H w := (hchart.comp w hcw).contDiffAt
  have hvel : fderiv ℝ H w ((1, 0), 0) ≠ 0 := by
    rw [chart_angular_derivative c w q hcw hwq]
    exact fun hz => hv ((mdifferentiable_chart (I := 𝓡 3) q).mfderiv_injective hwq
      (hz.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, (fderiv ℝ H w ((1, 0), 0)) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hvel (by ext i; exact h i)
  let h : ((ℝ × P) × ℝ) → ℝ := fun z => H z i
  have hh : ContDiffAt ℝ 1 h w :=
    (EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).contDiff.contDiffAt.comp w hH
  have hrow (z : (ℝ × P) × ℝ) (hz : ContDiffAt ℝ 1 H z) :
      fderiv ℝ h z ((1, 0), 0) = (fderiv ℝ H z ((1, 0), 0)) i := by
    exact congrArg (fun A : ((ℝ × P) × ℝ) →L[ℝ] ℝ => A ((1, 0), 0))
      (((EuclideanSpace.proj i).hasFDerivAt.comp z hz.differentiableAt_one.hasFDerivAt).fderiv)
  obtain ⟨V, hVo, hwV, hVrow, hVinj⟩ := scalar_angular_neighborhood h w hh
    (by rw [hrow w hH]; exact hi)
  have hcap : U ∩ c ⁻¹' e.source ∈ 𝓝 w :=
    inter_mem (hU.mem_nhds hw) (hcw.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hwq))
  obtain ⟨O, hO, hOo, hwO⟩ := _root_.mem_nhds_iff.mp hcap
  refine ⟨V ∩ O, hVo.inter hOo, ⟨hwV, hwO⟩, fun z hz => (hO hz.2).1, ?_, ?_⟩
  · intro z hz hzero
    have hzc := hc.contMDiffAt (hU.mem_nhds (hO hz.2).1)
    have hze : ContMDiffAt (𝓡 3) (𝓡 3) 1 e (c z) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) (hO hz.2).2
    have hHz : ContDiffAt ℝ 1 H z := (hze.comp z hzc).contDiffAt
    apply hVrow z hz.1
    rw [hrow z hHz, chart_angular_derivative c z q hzc (hO hz.2).2, hzero, map_zero]
    rfl
  · intro p t x hx y hy hxy
    apply hVinj p t hx.1 hy.1
    exact congrArg (fun z : M => e z i) hxy

end PoincareConjecture.M65Perturbation
