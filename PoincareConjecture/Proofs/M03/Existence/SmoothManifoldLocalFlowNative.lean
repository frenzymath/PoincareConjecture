import PoincareConjecture.Proofs.M03.Existence.SmoothLocalFlowNative
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Metric Manifold
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.SmoothManifoldLocalFlowNative

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "I" => 𝓘(ℝ, E)

def coordinateField (V : (x : M) → TangentSpace I x) (p : M) (y : E) : E :=
  tangentCoordChange I ((extChartAt I p).symm y) p ((extChartAt I p).symm y)
    (V ((extChartAt I p).symm y))

set_option backward.isDefEq.respectTransparency false in
theorem coordinateField_contDiffOn_of_order {k : ℕ∞}
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) (p : M) :
    ContDiffOn ℝ k (coordinateField V p) (extChartAt I p).target := by
  let e := trivializationAt E (TangentSpace I) p
  have hcoord : ContMDiffOn I 𝓘(ℝ, E) k
      (fun x => (e (⟨x, V x⟩ : TangentBundle I M)).2) e.baseSet :=
    e.contMDiffOn_section_baseSet_iff.mp hV.contMDiffOn
  have hcomp := hcoord.comp (contMDiffOn_extChartAt_symm p)
    (show MapsTo (extChartAt I p).symm (extChartAt I p).target e.baseSet by
      simpa only [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt I p).mapsTo_symm)
  apply hcomp.contDiffOn.congr
  intro y _
  rfl

theorem coordinateField_contDiffOn
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) (p : M) :
    ContDiffOn ℝ ∞ (coordinateField V p) (extChartAt I p).target :=
  coordinateField_contDiffOn_of_order V hV p

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
    ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using hderiv.hasFDerivAt

theorem exists_contDiff_local_flow {k : ℕ∞} (hk : k ≠ 0)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.prod I 𝓘(ℝ, E)) k
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > 0, ∃ α : M × ℝ → M,
      (∀ x ∈ U, α (x, 0) = x) ∧
      (∀ x ∈ U, IsMIntegralCurveOn (fun t => α (x, t)) V (Ioo (-ε) ε)) ∧
      ContMDiffOn (ModelWithCorners.prod I 𝓘(ℝ, ℝ)) I k α (U ×ˢ Ioo (-ε) ε) := by
  obtain ⟨r, hr, ε, hε, A, hzero, hder, hA⟩ :=
    SmoothLocalFlowNative.exists_contDiff_confined_local_flow_on hk
      (coordinateField V p) (by simpa using (chartAt E p).open_target)
      (coordinateField_contDiffOn_of_order V hV p) (extChartAt I p p)
      (mem_extChartAt_target p) (extChartAt_target_mem_nhds p)
  let U : Set M := (extChartAt I p).source ∩
    (extChartAt I p) ⁻¹' ball (extChartAt I p p) r
  have hUo : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hxchart : x ∈ (chartAt E p).source := by
      simpa only [extChartAt_source] using hx.1
    have hsource : (extChartAt I p).source ∈ 𝓝 x := by
      simpa only [extChartAt_source] using (chartAt E p).open_source.mem_nhds hxchart
    exact Filter.inter_mem hsource
      ((continuousAt_extChartAt' hx.1).preimage_mem_nhds (isOpen_ball.mem_nhds hx.2))
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, mem_ball_self hr⟩
  let α : M × ℝ → M := fun q => (extChartAt I p).symm (A (extChartAt I p q.1, q.2))
  refine ⟨U, hUo, hpU, ε, hε, α, ?_, ?_, ?_⟩
  · intro x hx
    change (extChartAt I p).symm (A (extChartAt I p x, 0)) = x
    rw [hzero _ hx.2, (extChartAt I p).left_inv hx.1]
  · intro x hx t ht
    obtain ⟨hd, htarget⟩ := hder _ hx.2 t ht
    exact (hasMFDerivAt_inverse_chart_curve htarget hd).hasMFDerivWithinAt
  · have hchart0 : ContMDiffOn I 𝓘(ℝ, E) k (extChartAt I p)
        (extChartAt I p).source := by
      rw [extChartAt_source]
      exact contMDiffOn_extChartAt
    have hchart : ContMDiffOn (ModelWithCorners.prod I 𝓘(ℝ, ℝ))
        𝓘(ℝ, E × ℝ) k
        (fun q : M × ℝ => (extChartAt I p q.1, q.2)) (U ×ˢ Ioo (-ε) ε) := by
      apply (contMDiffOn_prod_module_iff _).mpr
      exact ⟨hchart0.comp contMDiffOn_fst (fun q hq => hq.1.1), contMDiffOn_snd⟩
    have hcoord := hA.contMDiffOn.comp hchart (fun q hq => ⟨hq.1.2, hq.2⟩)
    exact (contMDiffOn_extChartAt_symm p).comp hcoord
      (fun q hq => (hder _ hq.1.2 _ hq.2).2)

theorem exists_smooth_local_flow
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle I M))) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > 0, ∃ α : M × ℝ → M,
      (∀ x ∈ U, α (x, 0) = x) ∧
      (∀ x ∈ U, IsMIntegralCurveOn (fun t => α (x, t)) V (Ioo (-ε) ε)) ∧
      ContMDiffOn (ModelWithCorners.prod I 𝓘(ℝ, ℝ)) I ∞ α (U ×ˢ Ioo (-ε) ε) :=
  exists_contDiff_local_flow (by simp) V hV p

end PoincareConjecture.SmoothManifoldLocalFlowNative

end
