import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcGraphNeighborhood
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopRegionChart
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.CollarCoordinates










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_exists_arc_region_chart
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b p : ℝ}
    (hinj : InjOn alpha (Icc a b)) (hp : p ∈ Ioo a b) (hregular : deriv alpha p ≠ 0)
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha p ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc a b ∪ W) (hfV : frontier V = frontier U) :
    ∃ H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ H.source ∧ H 0 = alpha p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target ∧
      (∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ frontier U ↔ z 1 = 0) ∧
      ((∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ 0 ≤ z 1) ∨
        (∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ z 1 ≤ 0)) := by
  obtain ⟨L, h, X, O, hX, hh, hO, hpO, hgraph⟩ :=
    m64Intrinsic_exists_arc_graph_neighborhood ha hinj hp hregular hW hpW
  obtain ⟨G, hsource, _, hformula, hG, hGi⟩ :=
    m64Intrinsic_graph_straightening_chart L hX hh
  let x := (L (alpha p)).1
  have hxX : x ∈ X := (hgraph (alpha p) hpO).1
  have hpgraph : (L (alpha p)).2 = h x :=
    (hgraph (alpha p) hpO).2.mp (Or.inl ⟨p, Ioo_subset_Icc_self hp, rfl⟩)
  have hx : (x, 0) ∈ G.source := by rw [hsource]; exact ⟨hxX, mem_univ _⟩
  have hbase : G (x, 0) = alpha p := by
    rw [hformula, add_zero]
    apply L.injective
    rw [L.apply_symm_apply]
    exact Prod.ext rfl hpgraph.symm
  have hpfront : G (x, 0) ∈ frontier U := by
    rw [hbase, hfU]
    exact Or.inl ⟨p, Ioo_subset_Icc_self hp, rfl⟩
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), G z ∈ O :=
    (G.continuousAt hx).preimage_mem_nhds (by simpa only [hbase] using hO.mem_nhds hpO)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), G z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [hfU, (hgraph (G z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  have hside := m64Intrinsic_jordan_product_line_germ hU hV hdisj hfV.symm G hx hpfront hline
  let e : AnnulusCoordinates ≃ₜ (ℝ × ℝ) :=
    collarParameterEquiv.toHomeomorph.trans (Homeomorph.addRight (x, 0))
  have he (z : AnnulusCoordinates) : e z = (z 0 + x, z 1) := by
    ext <;> simp [e, collarParameterEquiv]
  have he0 : e (0 : AnnulusCoordinates) = (x, 0) := by simp only [he]; simp
  have heSmooth : ContDiff ℝ ∞ e :=
    collarParameterEquiv.contDiff.add contDiff_const
  have heiSmooth : ContDiff ℝ ∞ e.symm :=
    collarParameterEquiv.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  let H := e.toOpenPartialHomeomorph.trans G
  have h0 : (0 : AnnulusCoordinates) ∈ H.source :=
    ⟨mem_univ _, by change e 0 ∈ G.source; rw [he0]; exact hx⟩
  have hH : ContDiffOn ℝ ∞ H H.source :=
    hG.comp heSmooth.contDiffOn (fun _ hz => hz.2)
  have hHi : ContDiffOn ℝ ∞ H.symm H.target :=
    heiSmooth.comp_contDiffOn (hGi.mono (fun _ hz => hz.1))
  have ht : Tendsto e (𝓝 (0 : AnnulusCoordinates)) (𝓝 (x, (0 : ℝ))) := by
    simpa only [he0] using e.continuous.tendsto (0 : AnnulusCoordinates)
  refine ⟨H, h0, ?_, contMDiffOn_iff_contDiffOn.mpr hH,
    contMDiffOn_iff_contDiffOn.mpr hHi, ?_, ?_⟩
  · change G (e 0) = alpha p
    rw [he0, hbase]
  · filter_upwards [ht.eventually hline] with z hz
    change G (e z) ∈ frontier U ↔ z 1 = 0
    simpa only [he] using hz
  · rcases hside with hpos | hneg
    · left
      filter_upwards [ht.eventually hpos] with z hz
      change G (e z) ∈ closure U ↔ 0 ≤ z 1
      simpa only [he] using hz
    · right
      filter_upwards [ht.eventually hneg] with z hz
      change G (e z) ∈ closure U ↔ z 1 ≤ 0
      simpa only [he] using hz

end PoincareConjecture
