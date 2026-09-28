import PoincareConjecture.Proofs.M03.Existence.UniformIntegralCurveNative
import PoincareConjecture.Proofs.M03.Existence.FiniteChartCommonTimeNative








set_option autoImplicit false

open Set Metric Manifold
open ContinuousLinearMap
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.CompactIntegralCurveNative

theorem exists_confined_local_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E,
      (∀ x ∈ ball x₀ r, α (x, 0) = x) ∧
      (∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t ∧ α (x, t) ∈ s) ∧
      ContinuousOn α (ball x₀ r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨δ, hδ, a, r₀, L, K, hr₀, hPL⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα, hcont⟩ :=
    (hPL 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hzero : α (x₀, 0) = x₀ := (hα x₀ (mem_closedBall_self hr₀.le)).1
  have hdomain : closedBall x₀ (r₀ : ℝ) ×ˢ Icc (0 - δ) (0 + δ) ∈
      𝓝 (x₀, (0 : ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds _ hr₀) (Icc_mem_nhds (by linarith) (by linarith))
  have hs' : α ⁻¹' s ∈ 𝓝 (x₀, (0 : ℝ)) :=
    (hcont.continuousAt hdomain).preimage_mem_nhds (hzero.symm ▸ hs)
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.mem_nhds_iff.mp
    (show α ⁻¹' s ∩ (closedBall x₀ (r₀ : ℝ) ×ˢ Icc (0 - δ) (0 + δ)) ∈
      𝓝 (x₀, (0 : ℝ)) from Filter.inter_mem hs' hdomain)
  let ε := min ρ δ
  have hε : 0 < ε := lt_min hρ hδ
  have hmem {x : E} (hx : x ∈ ball x₀ ρ) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
      (x, t) ∈ α ⁻¹' s ∩ (closedBall x₀ (r₀ : ℝ) ×ˢ Icc (0 - δ) (0 + δ)) := by
    apply hsmall
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨Metric.mem_ball.mp hx, ?_⟩
    rw [Real.dist_eq]
    have ht' : |(x, t).2 - (x₀, (0 : ℝ)).2| < ε := by
      simpa using (abs_lt.mpr ht)
    exact lt_of_lt_of_le ht' (min_le_left _ _)
  refine ⟨ρ, hρ, ε, hε, α, ?_, ?_, ?_⟩
  · intro x hx
    exact (hα x (hmem hx ⟨neg_lt_zero.mpr hε, hε⟩).2.1).1
  · intro x hx t ht
    have hm := hmem hx ht
    have htδ : t ∈ Ioo (0 - δ) (0 + δ) := by
      constructor
      · linarith [ht.1, min_le_right ρ δ]
      · linarith [ht.2, min_le_right ρ δ]
    refine ⟨((hα x hm.2.1).2 t hm.2.2).hasDerivAt (Icc_mem_nhds htδ.1 htδ.2), hm.1⟩
  · exact hcont.mono (fun xt hxt => (hmem hxt.1 hxt.2).2)

variable {n : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n
local notation "E" => EuclideanSpace ℝ (Fin n)

def coordinateField (V : (x : M) → TangentSpace I x) (p : M) (y : E) : E :=
  tangentCoordChange I ((extChartAt I p).symm y) p ((extChartAt I p).symm y)
    (V ((extChartAt I p).symm y))

set_option backward.isDefEq.respectTransparency false in
theorem coordinateField_contDiffAt
    {V : (x : M) → TangentSpace I x} {p : M}
    (hV : ContMDiffAt I (ModelWithCorners.tangent I) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) p) :
    ContDiffAt ℝ 1 (coordinateField V p) (extChartAt I p p) := by
  rw [contMDiffAt_iff] at hV
  exact (hV.2.contDiffAt (range_mem_nhds_isInteriorPoint
    BoundarylessManifold.isInteriorPoint)).snd

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_inverse_chart_curve
    {V : (x : M) → TangentSpace I x} {p : M} {u : ℝ → E} {t : ℝ}
    (htarget : u t ∈ (extChartAt I p).target)
    (hu : HasDerivAt u (coordinateField V p (u t)) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I ((extChartAt I p).symm ∘ u) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V ((extChartAt I p).symm (u t)))) := by
  let q := (extChartAt I p).symm (u t)
  have hqp : q ∈ (extChartAt I p).source := (extChartAt I p).map_target htarget
  have hqq : q ∈ (extChartAt I q).source := mem_extChartAt_source q
  have hchange : HasFDerivAt ((extChartAt I q) ∘ (extChartAt I p).symm)
      (tangentCoordChange I p q q) (u t) := by
    have h := hasFDerivWithinAt_tangentCoordChange
      (x := p) (y := q) (z := q) ⟨hqp, hqq⟩
    have h' := h.hasFDerivAt (by simp : range I ∈ 𝓝 (extChartAt I p q))
    simpa only [q, (extChartAt I p).right_inv htarget] using h'
  have hvelocity : tangentCoordChange I p q q (coordinateField V p (u t)) = V q := by
    change tangentCoordChange I p q q (tangentCoordChange I q p q (V q)) = V q
    rw [tangentCoordChange_comp ⟨⟨hqq, hqp⟩, hqq⟩, tangentCoordChange_self hqq]
  have hderiv := (hchange.comp_hasDerivAt t hu).congr_deriv hvelocity
  refine ⟨(continuousAt_extChartAt_symm'' htarget).comp hu.continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  simpa [q, extChartAt_coe, extChartAt_coe_symm, Function.comp_def,
    smulRight_one_eq_toSpanSingleton] using hderiv.hasFDerivAt

theorem exists_uniform_local_curves_at
    {V : (x : M) → TangentSpace I x} {p : M}
    (hV : ContMDiffAt I (ModelWithCorners.tangent I) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) p) :
    ∃ U ∈ 𝓝 p, ∃ ε > 0, ∀ x ∈ U, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ V (Ioo (-ε) ε) := by
  obtain ⟨r, hr, ε, hε, α, hzero, hα, _⟩ :=
    exists_confined_local_flow (coordinateField_contDiffAt hV) (extChartAt_target_mem_nhds p)
  let U := (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' ball (extChartAt I p p) r
  have hU : U ∈ 𝓝 p := Filter.inter_mem (extChartAt_source_mem_nhds p)
    ((continuousAt_extChartAt p).preimage_mem_nhds (ball_mem_nhds _ hr))
  refine ⟨U, hU, ε, hε, ?_⟩
  intro x hx
  refine ⟨fun t => (extChartAt I p).symm (α (extChartAt I p x, t)), ?_, ?_⟩
  · change (extChartAt I p).symm (α (extChartAt I p x, 0)) = x
    rw [hzero _ hx.2, (extChartAt I p).left_inv hx.1]
  · intro t ht
    obtain ⟨hderiv, htarget⟩ := hα _ hx.2 t ht
    exact (hasMFDerivAt_inverse_chart_curve htarget hderiv).hasMFDerivWithinAt

theorem exists_uniform_local_curves [CompactSpace M]
    {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    ∃ ε > 0, ∀ x : M, ∃ γ : ℝ → M,
      γ 0 = x ∧ IsMIntegralCurveOn γ V (Ioo (-ε) ε) := by
  classical
  choose U hU τ hτ hcurve using fun p : M => exists_uniform_local_curves_at (hV p)
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  obtain ⟨ε, hε, hbound⟩ := exists_common_positive_time s τ (fun p _ => hτ p)
  refine ⟨ε, hε, ?_⟩
  intro x
  have hx : x ∈ ⋃ p ∈ s, U p := by rw [hs]; trivial
  obtain ⟨p, hp, hxU⟩ := mem_iUnion₂.mp hx
  obtain ⟨γ, hzero, hγ⟩ := hcurve p x hxU
  refine ⟨γ, hzero, hγ.mono ?_⟩
  exact Ioo_subset_Ioo (neg_le_neg (hbound p hp)) (hbound p hp)

def uniformData [CompactSpace M]
    {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    UniformIntegralCurveNative.Data V where
  ε := (exists_uniform_local_curves hV).choose
  ε_pos := (exists_uniform_local_curves hV).choose_spec.1
  local_curve := (exists_uniform_local_curves hV).choose_spec.2

theorem exists_global_integralCurve [CompactSpace M] [T2Space M]
    {V : (x : M) → TangentSpace I x}
    (hV : ContMDiff I (ModelWithCorners.tangent I) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) (p : M) :
    ∃ γ : ℝ → M, γ 0 = p ∧ IsMIntegralCurve γ V :=
  UniformIntegralCurveNative.exists_global_orbit V hV (uniformData hV) p

end PoincareConjecture.CompactIntegralCurveNative

end
