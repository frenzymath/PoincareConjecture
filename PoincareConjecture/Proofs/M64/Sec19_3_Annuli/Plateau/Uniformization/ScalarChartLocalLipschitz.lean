import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarChartAreaStep
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
local notation "E" => EuclideanSpace ℝ (Fin n)

def ScalarLocallyChartLipschitz (f : Plane → M) (O : Set Plane) : Prop :=
  ∀ x ∈ O, ∃ L : ℝ≥0, ∃ V ∈ 𝓝 x, LipschitzOnWith L ((chartAt E (f x)) ∘ f) V

omit [IsManifold (𝓡 n) ∞ M] in

theorem scalar_coordinate_lipschitz_change_chart
    (e k : OpenPartialHomeomorph M E)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hk : ContMDiffOn (𝓡 n) (𝓡 n) 1 k k.source)
    {f : Plane → M} {x : Plane} {V : Set Plane} (hV : V ∈ 𝓝 x)
    (hfV : MapsTo f V e.source) {L : ℝ≥0}
    (hL : LipschitzOnWith L (e ∘ f) V) (hxk : f x ∈ k.source) :
    ∃ B : ℝ≥0, ∃ W ∈ 𝓝 x, LipschitzOnWith B (k ∘ f) W := by
  have hxe := hfV (mem_of_mem_nhds hV)
  have hkat : ContMDiffAt (𝓡 n) (𝓡 n) 1 k (e.symm (e (f x))) := by
    rw [e.left_inv hxe]
    exact hk.contMDiffAt (k.open_source.mem_nhds hxk)
  have ht : ContDiffAt ℝ 1 (k ∘ e.symm) (e (f x)) :=
    contMDiffAt_iff_contDiffAt.mp
      (hkat.comp _ (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hxe))))
  obtain ⟨B, W, hW, htL⟩ := ht.exists_lipschitzOnWith
  have hc : ContinuousAt (e ∘ f) x := hL.continuousOn.continuousAt hV
  refine ⟨B * L, V ∩ (e ∘ f) ⁻¹' W, inter_mem hV (hc.preimage_mem_nhds hW), ?_⟩
  have hcomp := htL.comp (hL.mono inter_subset_left) (fun _ hx => hx.2)
  intro y hy z hz
  have heqy : ((k ∘ e.symm) ∘ (e ∘ f)) y = (k ∘ f) y := by
    simp only [Function.comp_apply, e.left_inv (hfV hy.1)]
  have heqz : ((k ∘ e.symm) ∘ (e ∘ f)) z = (k ∘ f) z := by
    simp only [Function.comp_apply, e.left_inv (hfV hz.1)]
  simpa only [heqy, heqz] using hcomp hy hz

theorem ScalarLocallyChartLipschitz.in_chart
    {f : Plane → M} {O : Set Plane} (hlocal : ScalarLocallyChartLipschitz (n := n) f O)
    (hf : ContinuousOn f O) (hO : IsOpen O) {x : Plane} (hx : x ∈ O)
    (e : OpenPartialHomeomorph M E) (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hxe : f x ∈ e.source) :
    ∃ L : ℝ≥0, ∃ V ∈ 𝓝 x, LipschitzOnWith L (e ∘ f) V := by
  obtain ⟨L, V, hV, hL⟩ := hlocal x hx
  let c := chartAt E (f x)
  have hsource := (hf.continuousAt (hO.mem_nhds hx)).preimage_mem_nhds
    (c.open_source.mem_nhds (mem_chart_source E (f x)))
  exact scalar_coordinate_lipschitz_change_chart c e
    contMDiffOn_chart_symm he (inter_mem hV hsource)
    (fun _ hp => hp.2) (hL.mono inter_subset_left) hxe

theorem ScalarLocallyChartLipschitz.compact_patch
    {f : Plane → M} {O C : Set Plane} (hlocal : ScalarLocallyChartLipschitz (n := n) f O)
    (hf : ContinuousOn f O) (hO : IsOpen O) (hC : IsCompact C) (hCO : C ⊆ O)
    (e : OpenPartialHomeomorph M E) (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hCe : MapsTo f C e.source) :
    ∃ L : ℝ≥0, ∃ V : Set Plane, IsOpen V ∧ C ⊆ V ∧ V ⊆ O ∧
      MapsTo f V e.source ∧ LipschitzOnWith L (e ∘ f) V := by
  let U := O ∩ f ⁻¹' e.source
  have hU : IsOpen U := hf.isOpen_inter_preimage hO e.open_source
  obtain ⟨delta, hdelta, hmargin⟩ := hC.exists_cthickening_subset_open hU
    (fun _ hx => ⟨hCO hx, hCe hx⟩)
  let Q := Metric.cthickening delta C
  have hQ : IsCompact Q := hC.cthickening
  have hloc : LocallyLipschitzOn Q (e ∘ f) := by
    intro x hx
    obtain ⟨L, V, hV, hL⟩ := hlocal.in_chart hf hO (hmargin hx).1 e he (hmargin hx).2
    exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hQ
  refine ⟨L, interior Q, isOpen_interior, ?_,
    (fun _ hx => (hmargin (interior_subset hx)).1),
    (fun _ hx => (hmargin (interior_subset hx)).2), hL.mono interior_subset⟩
  exact (Metric.self_subset_thickening hdelta C).trans
    (Metric.thickening_subset_interior_cthickening delta C)

theorem ScalarLocallyChartLipschitz.of_chart_replacement
    {f F : Plane → M} {O V C : Set Plane}
    (hlocal : ScalarLocallyChartLipschitz (n := n) f O)
    (hV : IsOpen V) (hCV : C ⊆ V)
    (e : OpenPartialHomeomorph M E)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hFmap : MapsTo F V e.source) {L : ℝ≥0} (hL : LipschitzOnWith L (e ∘ F) V)
    (haway : ∀ x, x ∉ C → F =ᶠ[𝓝 x] f) :
    ScalarLocallyChartLipschitz (n := n) F O := by
  intro x hx
  by_cases hxC : x ∈ C
  · exact scalar_coordinate_lipschitz_change_chart e (chartAt E (F x)) hei
      contMDiffOn_chart (hV.mem_nhds (hCV hxC)) hFmap hL
      (mem_chart_source E (F x))
  · obtain ⟨L, W, hW, hLip⟩ := hlocal x hx
    have hsame := haway x hxC
    have hxvalue : F x = f x := hsame.self_of_nhds
    refine ⟨L, W ∩ {y | F y = f y}, inter_mem hW hsame, ?_⟩
    intro y hy z hz
    have hyvalue : F y = f y := hy.2
    have hzvalue : F z = f z := hz.2
    simpa only [Function.comp_apply, hxvalue, hyvalue, hzvalue] using hLip hy.1 hz.1

end PoincareConjecture.M64Uniformization
