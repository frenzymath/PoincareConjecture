import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.SliceChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

variable {m k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = m + k)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → Fin k → ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) ∞ f) (c : Fin k → ℝ)
  (hreg : ∀ x : M, f x = c → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Fin k → ℝ) f x))

def fiberChart (z : (f ⁻¹' {c} : Set M)) :
    OpenPartialHomeomorph (f ⁻¹' {c} : Set M) (EuclideanSpace ℝ (Fin m)) :=
  sliceChart f c (adaptedChart (m := m) hf z (hreg z z.2))
    (fun _ hy => comp_adaptedChart_symm hf z (hreg z z.2) hy) z

theorem mem_fiberChart_source (z : (f ⁻¹' {c} : Set M)) :
    z ∈ (fiberChart (m := m) hf c hreg z).source :=
  mem_adaptedChart_source hf z (hreg z z.2)

@[simp] theorem fiberChart_apply (z w : (f ⁻¹' {c} : Set M)) :
    fiberChart (m := m) hf c hreg z w =
      (adaptedChart (m := m) hf z (hreg z z.2) w).2 := rfl

theorem fiberChart_symm_val (z : (f ⁻¹' {c} : Set M))
    {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ (fiberChart (m := m) hf c hreg z).target) :
    ((fiberChart (m := m) hf c hreg z).symm y : M) =
      (adaptedChart (m := m) hf z (hreg z z.2)).symm (c, y) :=
  sliceChart_symm_val f c _ _ z hy

@[reducible] def fiberChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin m)) (f ⁻¹' {c} : Set M) where
  atlas := ⋃ z : (f ⁻¹' {c} : Set M), {fiberChart (m := m) hf c hreg z}
  chartAt := fiberChart (m := m) hf c hreg
  mem_chart_source := mem_fiberChart_source hf c hreg
  chart_mem_atlas z := mem_iUnion.mpr ⟨z, rfl⟩

theorem contDiffOn_fiberChart_trans (z w : (f ⁻¹' {c} : Set M)) :
    ContDiffOn ℝ ∞
      ((fiberChart (m := m) hf c hreg z).symm.trans (fiberChart (m := m) hf c hreg w))
      ((fiberChart (m := m) hf c hreg z).symm.trans (fiberChart (m := m) hf c hreg w)).source := by
  intro y hy
  let e := adaptedChart (m := m) hf z (hreg z z.2)
  let e' := adaptedChart (m := m) hf w (hreg w w.2)
  have hyT : (c, y) ∈ e.target := hy.1
  have hyS : e.symm (c, y) ∈ e'.source := by
    have h := hy.2
    change ((fiberChart (m := m) hf c hreg z).symm y : M) ∈ e'.source at h
    rwa [fiberChart_symm_val hf c hreg z hy.1] at h
  have hpair : ContMDiffAt (𝓡 m)
      𝓘(ℝ, (Fin k → ℝ) × EuclideanSpace ℝ (Fin m)) ∞ (fun v => (c, v)) y :=
    (contDiff_const.prodMk contDiff_id).contDiffAt.contMDiffAt
  have hinv := (contMDiffOn_adaptedChart_symm hf z (hreg z z.2)).contMDiffAt
    (e.open_target.mem_nhds hyT)
  have hforward := (contMDiffOn_adaptedChart hf w (hreg w w.2)).contMDiffAt
    (e'.open_source.mem_nhds hyS)
  have hcomp : ContMDiffAt (𝓡 m) (𝓡 m) ∞ (fun v => (e' (e.symm (c, v))).2) y :=
    contDiff_snd.contDiffAt.contMDiffAt.comp y (hforward.comp y (hinv.comp y hpair))
  refine (contMDiffAt_iff_contDiffAt.mp hcomp).contDiffWithinAt.congr ?_ ?_
  · intro v hv
    rw [OpenPartialHomeomorph.trans_apply, fiberChart_apply,
      fiberChart_symm_val hf c hreg z hv.1]
  · rw [OpenPartialHomeomorph.trans_apply, fiberChart_apply,
      fiberChart_symm_val hf c hreg z hy.1]

theorem isManifold_fiber :
    let := fiberChartedSpace (m := m) hf c hreg
    IsManifold (𝓡 m) ∞ (f ⁻¹' {c} : Set M) := by
  let := fiberChartedSpace (m := m) hf c hreg
  refine isManifold_of_contDiffOn (𝓡 m) ∞ (f ⁻¹' {c} : Set M) ?_
  intro e e' he he'
  obtain ⟨z, hz⟩ := mem_iUnion.mp he
  obtain ⟨w, hw⟩ := mem_iUnion.mp he'
  rw [mem_singleton_iff] at hz hw
  subst e e'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.inter_univ, Set.preimage_id, Function.comp_def, id_eq]
  exact contDiffOn_fiberChart_trans hf c hreg z w

end Poincare.Geometry.Manifold.RegularFiber
