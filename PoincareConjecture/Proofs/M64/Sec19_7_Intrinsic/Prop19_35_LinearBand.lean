import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphCapFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Polygonal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_linear_band
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ) (X : Set ℝ)
      (a b d : ℝ) (hab : a < b)
      (B : SmoothGraphBandPair
        (collarParameterEquiv.trans L.symm).toHomeomorph.toOpenPartialHomeomorph
        h (fun _ => d) hab)
      (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ)) (W : Set AnnulusCoordinates),
      IsOpen X ∧ ContDiffOn ℝ ∞ h X ∧ Icc a b ⊆ X ∧
      IsCompact (B.lower.carrier ∪ B.upper.carrier) ∧
      B.lower.carrier ∪ B.upper.carrier ⊆ closure U ∧
      frontier (B.lower.carrier ∪ B.upper.carrier) ⊆
        frontier U ∪ ⋃ l ∈ lines, {z | l z = 0} ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      (B.lower.boundary 2).map '' Icc (0 : ℝ) 1 ⊆ frontier U ∧
      (∃ t ∈ Ioo (0 : ℝ) 1, (B.lower.boundary 2).map t = gamma p) ∧
      IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ B.lower.carrier ∪ B.upper.carrier := by
  obtain ⟨L, h, X, x, a, b, d, W, hX, hh, hbase, ha, hb, hI, hgap,
      hgraph, hcompact, hsub, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_loop_graph_cap hg hend hinj hp hregular hU hV hdisj hfU hfV
  let A := collarParameterEquiv.trans L.symm
  let F := A.toHomeomorph.toOpenPartialHomeomorph
  have hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source :=
    contMDiffOn_iff_contDiffOn.mpr A.contDiff.contDiffOn
  have hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target :=
    contMDiffOn_iff_contDiffOn.mpr A.symm.contDiff.contDiffOn
  have hab : a < b := ha.trans hb
  obtain ⟨B⟩ := exists_smoothGraphBandPair F hF hFi hX hh
    (contDiffOn_const (c := d)) hab hI hgap (fun z _ => mem_univ z)
      (0 : AnnulusCoordinates) (by intro z _; simp)
  have hB : B.lower.carrier ∪ B.upper.carrier =
      L.symm '' {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ h q.1 ≤ q.2 ∧ q.2 ≤ d} := by
    rw [B.cover]
    ext z
    constructor
    · rintro ⟨q, hq, heq⟩
      exact ⟨collarParameterEquiv q, hq, heq⟩
    · rintro ⟨q, hq, heq⟩
      refine ⟨collarParameterEquiv.symm q, ?_, ?_⟩
      · change collarParameterEquiv (collarParameterEquiv.symm q) ∈
          {v : ℝ × ℝ | v.1 ∈ Icc a b ∧ h v.1 ≤ v.2 ∧ v.2 ≤ d}
        rw [collarParameterEquiv.apply_symm_apply]
        exact hq
      · change L.symm (collarParameterEquiv (collarParameterEquiv.symm q)) = z
        rw [collarParameterEquiv.apply_symm_apply]
        exact heq
  have hboundary (t : ℝ) : (B.lower.boundary 2).map t =
      L.symm (a + t * (b - a), h (a + t * (b - a))) := by
    rw [B.lower_edge]
    change L.symm (collarParameterEquiv
      (collarParameterEquiv.symm (a + t * (b - a), h (a + t * (b - a))))) = _
    rw [collarParameterEquiv.apply_symm_apply]
  obtain ⟨lines, hlines, hlineeq⟩ := m64Intrinsic_graph_cap_interface_lines L a b d
  refine ⟨L, h, X, a, b, d, hab, B, lines, W, hX, hh, hI, hB ▸ hcompact,
    hB ▸ hsub, ?_, hlines, ?_, ?_, hW, hpW, hB ▸ hcover⟩
  · rw [hB, ← hlineeq]
    exact m64Intrinsic_graph_cap_frontier_subset L hX hh hI hgraph hcompact
  · rintro z ⟨t, ht, rfl⟩
    rw [hboundary]
    apply hgraph
    constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab.le),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab.le)]
  · let t := (x - a) / (b - a)
    have hba : 0 < b - a := sub_pos.mpr hab
    have ht : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (sub_pos.mpr ha) hba, (div_lt_one hba).mpr (by linarith)⟩
    have hparam : a + t * (b - a) = x := by
      dsimp [t]
      rw [div_mul_cancel₀ _ hba.ne']
      ring
    refine ⟨t, ht, ?_⟩
    rw [hboundary, hparam, ← hbase, L.symm_apply_apply]

end PoincareConjecture
