import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopGraphNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JordanLineGerm
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Strip

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_graph_straightening_chart
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) {h : ℝ → ℝ} {X : Set ℝ}
    (hX : IsOpen X) (hh : ContDiffOn ℝ ∞ h X) :
    ∃ H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates,
      H.source = X ×ˢ univ ∧ H.target = {z | (L z).1 ∈ X} ∧
      (∀ q : ℝ × ℝ, H q = L.symm (q.1, h q.1 + q.2)) ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target := by
  have hh1 : ContDiffOn ℝ ∞ (fun x => h x + 1) X := hh.add contDiffOn_const
  have hgap : ∀ x ∈ X, h x < h x + 1 := by intro x _; linarith
  let G := graphStripCoordinates hX hh hh1 hgap
  let H := G.trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsource : H.source = X ×ˢ univ := by
    ext q
    simp [H, G, graphStripCoordinates]
  have htarget : H.target = {z | (L z).1 ∈ X} := by
    ext z
    simp [H, G, graphStripCoordinates]
  have hformula (q : ℝ × ℝ) : H q = L.symm (q.1, h q.1 + q.2) := by
    change L.symm (graphStripMap h (fun x => h x + 1) q) = _
    congr 1
    ext <;> simp [graphStripMap]
  refine ⟨H, hsource, htarget, hformula, ?_, ?_⟩
  · change ContDiffOn ℝ ∞ (L.symm ∘ graphStripMap h (fun x => h x + 1)) H.source
    rw [hsource]
    exact L.symm.contDiff.comp_contDiffOn (contDiffOn_graphStripMap hh hh1)
  · change ContDiffOn ℝ ∞ (graphStripInv h (fun x => h x + 1) ∘ L) H.target
    apply (contDiffOn_graphStripInv hh hh1 hgap).comp L.contDiff.contDiffOn
    intro z hz
    rw [htarget] at hz
    exact ⟨hz, mem_univ _⟩

theorem m64Intrinsic_exists_loop_region_straightening
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (x : ℝ),
      (x, 0) ∈ H.source ∧ H (x, 0) = gamma p ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      ((∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ 0 ≤ z.2) ∨
        (∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ closure U ↔ z.2 ≤ 0)) := by
  obtain ⟨L, h, X, W, hX, hh, hW, hpW, hWgraph⟩ :=
    m64Intrinsic_exists_regular_loop_graph_neighborhood hg hend hinj hp hregular
  obtain ⟨H, hsource, _, hformula, hH, hHi⟩ := m64Intrinsic_graph_straightening_chart L hX hh
  let x := (L (gamma p)).1
  have hxX : x ∈ X := (hWgraph (gamma p) hpW).1
  have hpgraph : (L (gamma p)).2 = h x :=
    (hWgraph (gamma p) hpW).2.mp ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  have hx : (x, 0) ∈ H.source := by
    rw [hsource]
    exact ⟨hxX, mem_univ _⟩
  have hbase : H (x, 0) = gamma p := by
    rw [hformula, add_zero]
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl hpgraph.symm
  have hpfront : H (x, 0) ∈ frontier U := by
    rw [hbase, hfU]
    exact ⟨p, ⟨hp.1.le, hp.2.le⟩, rfl⟩
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ W :=
    (H.continuousAt hx).preimage_mem_nhds (by simpa only [hbase] using hW.mem_nhds hpW)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [hfU, (hWgraph (H z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  exact ⟨H, x, hx, hbase, hH, hHi,
    m64Intrinsic_jordan_product_line_germ hU hV hdisj (hfU.trans hfV.symm) H hx hpfront hline⟩

end PoincareConjecture
