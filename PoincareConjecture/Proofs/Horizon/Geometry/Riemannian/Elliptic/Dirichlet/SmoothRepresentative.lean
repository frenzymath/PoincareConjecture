import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation
import Mathlib.Topology.Metrizable.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Manifold ContDiff InnerProductSpace Topology Bundle ENNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

set_option backward.isDefEq.respectTransparency false in
private theorem isSeparable_of_hausdorffMeasure_lt_top
    {X : Type u} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {s : Set X} (hs : Measure.hausdorffMeasure d s < ⊤) :
    IsSeparable s := by
  classical
  suffices h : ∀ ε > 0, ∃ c : Set X, c.Countable ∧
      s ⊆ ⋃ x ∈ c, Metric.closedEBall x ε by
    obtain ⟨c, -, hc, hsc⟩ := EMetric.subset_countable_closure_of_almost_dense_set s h
    exact ⟨c, hc, hsc⟩
  intro ε hε
  have hcover : (⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n)
      (_ : ∀ n, Metric.ediam (t n) ≤ ε),
      ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d) < ⊤ := by
    apply lt_of_le_of_lt ?_ hs
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le ε hε le_rfl
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp hcover
  obtain ⟨hst, ht⟩ := iInf_lt_iff.mp ht
  obtain ⟨htε, -⟩ := iInf_lt_iff.mp ht
  let ι := {n : ℕ // (t n).Nonempty}
  let c : ι → X := fun i => i.2.choose
  refine ⟨range c, countable_range c, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hst hx)
  let j : ι := ⟨i, ⟨x, hi⟩⟩
  exact mem_iUnion₂.mpr ⟨c j, mem_range_self j,
    (Metric.edist_le_ediam_of_mem hi j.2.choose_spec).trans (htε i)⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

private theorem isSeparable_of_volumeMeasure_lt_top
    {s : Set M} (hs : g.volumeMeasure s < ⊤) : IsSeparable s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply isSeparable_of_hausdorffMeasure_lt_top (d := n)
  change Measure.euclideanHausdorffMeasure n s < ⊤ at hs
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] at hs
  rcases ENNReal.mul_lt_top_iff.mp hs with h | h | h
  · exact h.2
  · exact (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
      (ENNReal.coe_eq_zero.mp h)).elim
  · simp [h]

private theorem isSeparable_support_L2 (f : Lp ℝ 2 g.volumeMeasure) :
    IsSeparable (Function.support (f : M → ℝ)) := by
  have hsep (k : ℕ) : IsSeparable {x : M | 1 / (k + 1 : ℝ) ≤ f x ^ 2} :=
    isSeparable_of_volumeMeasure_lt_top
      ((Lp.memLp f).integrable_sq.measure_ge_lt_top (by positivity))
  apply (IsSeparable.iUnion hsep).mono
  intro x hx
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sq_pos_of_ne_zero hx)
  exact mem_iUnion.mpr ⟨k, hk.le⟩

theorem exists_smooth_representative_of_local (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 g.volumeMeasure)
    (hlocal : ∀ x ∈ Ω, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      ∃ F : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ F V ∧
        F =ᵐ[g.volumeMeasure.restrict V] (f : M → ℝ)) :
    ∃ U : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω ∧
      U =ᵐ[g.volumeMeasure.restrict Ω] (f : M → ℝ) := by
  classical
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  choose V hVo hxV hVΩ F hFs hFae using fun x : Ω => hlocal x x.2
  have hcompat (i j : Ω) : EqOn (F i) (F j) (V i ∩ V j) := by
    apply Measure.eqOn_open_of_ae_eq (μ := g.volumeMeasure)
      (Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hFae i))
        (Filter.EventuallyEq.symm
          (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hFae j))))
      ((hVo i).inter (hVo j))
      ((hFs i).continuousOn.mono inter_subset_left)
      ((hFs j).continuousOn.mono inter_subset_right)
  let U : M → ℝ := fun x => if hx : x ∈ Ω then F ⟨x, hx⟩ x else 0
  have hUF (i : Ω) : EqOn U (F i) (V i) := by
    intro x hx
    have hxΩ := hVΩ i hx
    simpa only [U, dif_pos hxΩ] using
      hcompat ⟨x, hxΩ⟩ i ⟨hxV ⟨x, hxΩ⟩, hx⟩
  have hUs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω := by
    intro x hx
    let i : Ω := ⟨x, hx⟩
    have heq : U =ᶠ[𝓝 x] F i :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨V i, (hVo i).mem_nhds (hxV i), hUF i⟩
    exact ((hFs i).contMDiffAt ((hVo i).mem_nhds (hxV i))).congr_of_eventuallyEq
      heq |>.contMDiffWithinAt
  have hUae (i : Ω) : U =ᵐ[g.volumeMeasure.restrict (V i)] (f : M → ℝ) :=
    Filter.EventuallyEq.trans
      ((ae_restrict_iff' (hVo i).measurableSet).mpr (ae_of_all _ (hUF i))) (hFae i)
  have hzero (x : M) (hx : x ∈ Ω) (hs : x ∉ closure (Function.support (f : M → ℝ))) :
      U x = 0 := by
    let i : Ω := ⟨x, hx⟩
    let W := V i ∩ (closure (Function.support (f : M → ℝ)))ᶜ
    have hWo : IsOpen W := (hVo i).inter isClosed_closure.isOpen_compl
    have hWΩ : W ⊆ Ω := inter_subset_left.trans (hVΩ i)
    have hWae : U =ᵐ[g.volumeMeasure.restrict W] (0 : M → ℝ) := by
      apply Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hUae i))
      apply (ae_restrict_iff' hWo.measurableSet).mpr
      exact ae_of_all _ fun y hy =>
        Function.notMem_support.mp (fun h => hy.2 (subset_closure h))
    exact Measure.eqOn_open_of_ae_eq (μ := g.volumeMeasure) hWae hWo
      (hUs.continuousOn.mono hWΩ)
      continuousOn_const ⟨hxV i, hs⟩
  let S := closure (Function.support (f : M → ℝ)) ∩ Ω
  have hSsep : IsSeparable S := (isSeparable_support_L2 f).closure.mono inter_subset_left
  let : SecondCountableTopology S := hSsep.secondCountableTopology
  have hSL : IsLindelof S := IsLindelof.of_coe
  obtain ⟨J, hJc, hJS⟩ := hSL.elim_countable_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx.2⟩, hxV ⟨x, hx.2⟩⟩)
  have : Countable J := hJc.to_subtype
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ j : J, x ∈ V j.1 → U x = f x :=
    ae_all_iff.mpr fun j => ae_imp_of_ae_restrict (hUae j.1)
  refine ⟨U, hUs, (ae_restrict_iff' hΩ.measurableSet).mpr ?_⟩
  filter_upwards [hall] with x hx hxΩ
  by_cases hxS : x ∈ closure (Function.support (f : M → ℝ))
  · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hJS ⟨hxS, hxΩ⟩)
    exact hx ⟨i, hi⟩ hxi
  · rw [hzero x hxΩ hxS, Function.notMem_support.mp (fun h => hxS (subset_closure h))]

end PoincareConjecture.LeviCivitaData.Dirichlet
