import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.LoopTopology
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option autoImplicit false

open Set Filter Bundle
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

private theorem tangentChart_eq (p : M) (q : TangentBundle (𝓡 3) M)
    (hq : q.1 ∈ (chartAt LoopAmbient p).source) :
    (chartAt (ModelProd LoopAmbient LoopAmbient)
      (⟨p, 0⟩ : TangentBundle (𝓡 3) M)) q =
      ((chartAt LoopAmbient p) q.1,
        mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p) q.1 q.2) := by
  have h := tangentMap_chart (I := 𝓡 3)
    (p := (⟨p, 0⟩ : TangentBundle (𝓡 3) M)) (q := q) hq
  exact (congrArg (TotalSpace.toProd LoopAmbient LoopAmbient) h).symm

theorem m65TangentBundle_tendsto_of_chart {ι : Type*} {l : Filter ι}
    (q : ι → TangentBundle (𝓡 3) M) (q0 : TangentBundle (𝓡 3) M) (p : M)
    (h0 : q0.1 ∈ (chartAt LoopAmbient p).source)
    (hq : ∀ᶠ i in l, (q i).1 ∈ (chartAt LoopAmbient p).source)
    (hvalue : Tendsto (fun i => (chartAt LoopAmbient p) (q i).1) l
      (𝓝 ((chartAt LoopAmbient p) q0.1)))
    (hvector : Tendsto (fun i =>
      mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p) (q i).1 (q i).2) l
      (𝓝 (mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p) q0.1 q0.2))) :
    Tendsto q l (𝓝 q0) := by
  let C := chartAt (ModelProd LoopAmbient LoopAmbient)
    (⟨p, 0⟩ : TangentBundle (𝓡 3) M)
  have hsource : q0 ∈ C.source := (TangentBundle.mem_chart_source_iff q0 ⟨p, 0⟩).mpr h0
  have hchart : Tendsto (fun i => C (q i)) l (𝓝 (C q0)) := by
    rw [show C q0 = _ from tangentChart_eq p q0 h0]
    exact (hvalue.prodMk_nhds hvector).congr'
      (hq.mono (fun i hi => (tangentChart_eq p (q i) hi).symm))
  have hinverse := (C.continuousAt_symm (C.map_source hsource)).tendsto.comp hchart
  rw [C.left_inv hsource] at hinverse
  exact hinverse.congr' (hq.mono (fun i hi =>
    C.left_inv ((TangentBundle.mem_chart_source_iff (q i) ⟨p, 0⟩).mpr hi)))

private theorem chart_curveVelocity (c : ℝ → M)
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c) (p : M) (x : ℝ)
    (hx : c x ∈ (chartAt LoopAmbient p).source) :
    mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p) (c x) (curveVelocity c x) =
      deriv (fun y => (chartAt LoopAmbient p) (c y)) x := by
  have h := mfderiv_comp_apply (f := c) (g := chartAt LoopAmbient p) x
    (mdifferentiableAt_atlas (chart_mem_atlas LoopAmbient p) hx)
    (hc.contMDiffAt.mdifferentiableAt one_ne_zero) (1 : ℝ)
  simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, Function.comp_def,
    curveVelocity] using! h.symm

theorem m65CurveTangent_tendsto_of_chart {ι : Type*} {l : Filter ι}
    (c : ι → ℝ → M) (c0 : ℝ → M)
    (hc : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (c i))
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 c0)
    (x0 : ℝ) (p : M) (h0 : c0 x0 ∈ (chartAt LoopAmbient p).source)
    (hbase : Tendsto (fun q : ι × ℝ => c q.1 q.2) (l ×ˢ 𝓝 x0) (𝓝 (c0 x0)))
    (hderiv : Tendsto (fun q : ι × ℝ =>
      deriv (fun y => (chartAt LoopAmbient p) (c q.1 y)) q.2) (l ×ˢ 𝓝 x0)
      (𝓝 (deriv (fun y => (chartAt LoopAmbient p) (c0 y)) x0))) :
    Tendsto (fun q : ι × ℝ =>
      (⟨c q.1 q.2, curveVelocity (c q.1) q.2⟩ : TangentBundle (𝓡 3) M))
      (l ×ˢ 𝓝 x0) (𝓝 (⟨c0 x0, curveVelocity c0 x0⟩ : TangentBundle (𝓡 3) M)) := by
  have hsrc := hbase.eventually ((chartAt LoopAmbient p).open_source.mem_nhds h0)
  apply m65TangentBundle_tendsto_of_chart _ _ p h0 hsrc
  · exact ((chartAt LoopAmbient p).continuousAt h0).tendsto.comp hbase
  · rw [chart_curveVelocity c0 hc0 p x0 h0]
    exact hderiv.congr' (hsrc.mono (fun q hq =>
      (chart_curveVelocity (c q.1) (hc q.1) p q.2 hq).symm))

end PoincareConjecture
