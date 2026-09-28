import PoincareConjecture.Proofs.M60.Mathlib.LipschitzDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle NNReal

namespace PoincareConjecture

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) M]



theorem m67_norm_mfderiv_apply_le_of_lipschitzOn {f : E → M} {S : Set E}
    (hS : IsOpen S) {K : ℝ≥0} (hf : LipschitzOnWith K f S)
    {z : E} (hz : z ∈ S) (v : E) :
    ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v‖ ≤ (K : ℝ) * ‖v‖ := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f z
  · apply (le_iff_forall_one_lt_le_mul₀ (mul_nonneg K.coe_nonneg (norm_nonneg v))).mpr
    intro c hc
    let C : ℝ≥0 := ⟨c, zero_lt_one.trans hc |>.le⟩
    have hC : 1 < C := hc
    let e := chartAt F (f z)
    have he : e.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) := mdifferentiable_chart (f z)
    have hx : f z ∈ e.source := mem_chart_source F (f z)
    let n := M40.normalizedSmoothChart e he hx
    have hn : f z ∈ n.source := by
      simpa only [n, M40.normalizedSmoothChart_source] using hx
    have hns : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, TangentSpace 𝓘(ℝ, F) (f z)) ∞ n n.source :=
      M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart
    obtain ⟨R, hR, _, _, hLip⟩ :=
      M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
        contMDiffOn_chart contMDiffOn_chart_symm C hC
    have hN : n.symm '' Metric.ball (n (f z)) R ∈ 𝓝 (f z) := by
      simpa only [n.left_inv hn] using
        n.symm.image_mem_nhds (n.map_source hn) (Metric.ball_mem_nhds _ hR)
    let U := S ∩ f ⁻¹' (n.symm '' Metric.ball (n (f z)) R)
    have hU : U ∈ 𝓝 z := inter_mem (hS.mem_nhds hz)
      (hd.continuousAt.preimage_mem_nhds hN)
    have hcomp : LipschitzOnWith (C * K) (n ∘ f) U :=
      hLip.comp (hf.mono inter_subset_left) (fun _ hu => hu.2)
    have hbound := norm_fderiv_le_of_lipschitzOn ℝ hU hcomp
    have hnd := (hns.contMDiffAt (n.open_source.mem_nhds hn)).mdifferentiableAt
      (by norm_num)
    have hchain : fderiv ℝ (n ∘ f) z v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v := by
      have hc := M40.normalizedSmoothChart_mfderiv_apply e he hx
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f z v)
      rw [← mfderiv_comp_apply z hnd hd, mfderiv_eq_fderiv] at hc
      exact hc
    rw [← hchain]
    calc
      _ ≤ ‖fderiv ℝ (n ∘ f) z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((C * K : ℝ≥0) : ℝ) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
      _ = _ := by change (c * (K : ℝ)) * ‖v‖ = _; ring
  · rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    erw [zero_apply, norm_zero]
    positivity

end PoincareConjecture


namespace PoincareConjecture

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [EMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
  [EMetricSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : N → Type _)]
  [IsRiemannianManifold 𝓘(ℝ, F) N]



theorem m67_norm_mfderiv_apply_le_of_lipschitz
    {f : M → N} (hd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) f)
    {K : ℝ≥0} (hf : LipschitzWith K f) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v‖ ≤ (K : ℝ) * ‖v‖ := by
  apply (le_iff_forall_one_lt_le_mul₀ (mul_nonneg K.coe_nonneg (norm_nonneg v))).mpr
  intro c hc
  let C : ℝ≥0 := ⟨c, zero_lt_one.trans hc |>.le⟩
  have hC : 1 < C := hc
  let e := chartAt E x
  have he : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := mdifferentiable_chart x
  have hx : x ∈ e.source := mem_chart_source E x
  let n := M40.normalizedSmoothChart e he hx
  have hn : x ∈ n.source := by
    simpa only [n, M40.normalizedSmoothChart_source] using hx
  have hns := M40.normalizedSmoothChart_contMDiffOn e he hx contMDiffOn_chart
  have hni := M40.normalizedSmoothChart_symm_contMDiffOn
    e he hx contMDiffOn_chart_symm
  obtain ⟨R, hR, htarget, hLip, _⟩ :=
    M40.normalizedSmoothChart_exists_lipschitz_ball e he hx
      contMDiffOn_chart contMDiffOn_chart_symm C hC
  have hcomp : LipschitzOnWith (K * C) (f ∘ n.symm) (Metric.ball (n x) R) :=
    hf.comp_lipschitzOnWith hLip
  have hb := m67_norm_mfderiv_apply_le_of_lipschitzOn (F := F) Metric.isOpen_ball hcomp
    (Metric.mem_ball_self hR) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) n x v)
  have hnd := (hns.contMDiffAt (n.open_source.mem_nhds hn)).mdifferentiableAt
    (by norm_num)
  have hnid := (hni.contMDiffAt
    (n.open_target.mem_nhds (n.map_source hn))).mdifferentiableAt (by norm_num)
  have hlocal : (f ∘ n.symm) ∘ n =ᶠ[𝓝 x] f := by
    filter_upwards [n.open_source.mem_nhds hn] with y hy
    exact congrArg f (n.left_inv hy)
  have hchain := mfderiv_comp x ((hd _).comp (n x) hnid) hnd
  rw [hlocal.mfderiv_eq] at hchain
  have hnorm : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) n x v‖ = ‖v‖ := by
    rw [norm_tangentSpace_vectorSpace]
    exact congrArg norm (M40.normalizedSmoothChart_mfderiv_apply e he hx v)
  have hb' : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v‖ ≤
      ((K * C : ℝ≥0) : ℝ) * ‖v‖ := by
    have hnorm_target (w : TangentSpace 𝓘(ℝ, F) (f x)) :
        ‖(show TangentSpace 𝓘(ℝ, F) (f (n.symm (n x))) from w)‖ = ‖w‖ := by
      rw [n.left_inv hn]
    rw [hnorm_target, hnorm] at hb
    have happ := congrArg (fun L => L v) hchain
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v =
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, F) (f ∘ n.symm) (n x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) n x v) at happ
    rw [← happ] at hb
    exact hb
  calc
    _ ≤ ((K * C : ℝ≥0) : ℝ) * ‖v‖ := hb'
    _ = _ := by change ((K : ℝ) * c) * ‖v‖ = _; ring

end PoincareConjecture
