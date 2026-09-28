import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReflexCornerFrontier













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface

namespace PoincareConjecture




theorem m64Intrinsic_exists_loop_corner_patch
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (A : Set AnnulusCoordinates) (lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ))
      (W : Set AnnulusCoordinates),
      IsCompact A ∧ A ⊆ closure U ∧
      frontier A ⊆ gamma '' Icc 0 T ∪ ⋃ l ∈ lines, {z | l z = 0} ∧
      (∀ l ∈ lines, Function.Surjective l) ∧
      IsOpen W ∧ gamma 0 ∈ W ∧ W ∩ closure U ⊆ A := by
  obtain ⟨G, hG0, hbase, hG, hGi, haxis, haxis', hside⟩ :=
    m64Intrinsic_exists_loop_corner_region hg hT hend hinj hind hU hV hdisj hfU hfV
  let e := collarParameterEquiv.symm
  let H := e.toHomeomorph.toOpenPartialHomeomorph.trans G
  have h0 : (0 : ℝ × ℝ) ∈ H.source := by
    refine ⟨mem_univ _, ?_⟩
    change e 0 ∈ G.source
    simpa only [map_zero] using hG0
  have hH : ContDiffOn ℝ ∞ H H.source :=
    (contMDiffOn_iff_contDiffOn.mp hG).comp e.contDiff.contDiffOn (fun _ hz => hz.2)
  have hHi : ContDiffOn ℝ ∞ H.symm H.target :=
    e.symm.contDiff.comp_contDiffOn
      ((contMDiffOn_iff_contDiffOn.mp hGi).mono (fun _ hz => hz.1))
  have hbase' : H 0 = gamma 0 := by
    change G (e 0) = gamma 0
    simpa only [map_zero] using hbase
  have haxisH (s : ℝ) : H (s, 0) = gamma s := by
    simpa [H, e, collarParameterEquiv] using haxis s
  have haxisH' (s : ℝ) : H (0, s) = gamma (T - s) := by
    simpa [H, e, collarParameterEquiv] using haxis' s
  have he : Tendsto e (𝓝 0) (𝓝 (0 : AnnulusCoordinates)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ℝ × ℝ)
  rcases hside with hpos | hneg
  · have hpos' : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ closure U ↔ 0 ≤ z.1 ∧ 0 ≤ z.2 := by
      simpa [H, e, collarParameterEquiv] using he.eventually hpos
    obtain ⟨r, face, W, hr, hrT, hsub, hsecond, hfirst, hchord, _, hW, hpW, hcover⟩ :=
      m64Intrinsic_exists_fitted_corner_face_le H h0 hH hHi hpos' hT
    obtain ⟨l, hl, hline⟩ := m64Intrinsic_corner_face_chord_line hchord
    have hfront := m64Intrinsic_corner_face_frontier_subset hr hrT haxisH haxisH'
      hfirst hsecond
    refine ⟨face.carrier, [l], W, face.isCompact_carrier_image, hsub, ?_, ?_,
      hW, hbase' ▸ hpW, hcover⟩
    · intro z hz
      rcases hfront hz with hzloop | hzline
      · exact Or.inl hzloop
      · exact Or.inr (mem_iUnion.mpr ⟨l, mem_iUnion.mpr ⟨by simp, hline hzline⟩⟩)
    · intro l' hl'
      simpa only [List.mem_singleton.mp hl'] using hl
  · have hneg' : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), H z ∈ closure U ↔ z.1 ≤ 0 ∨ z.2 ≤ 0 := by
      simpa [H, e, collarParameterEquiv] using he.eventually hneg
    obtain ⟨face, lines, W, hcompact, hsub, _, hfront, hlines, hW, hpW, hcover, _⟩ :=
      m64Intrinsic_exists_reflex_loop_corner_patch H h0 hH hHi hneg' hT haxisH haxisH'
    refine ⟨⋃ i, (face i).carrier, List.ofFn lines, W, hcompact, iUnion_subset hsub,
      ?_, ?_, hW, hbase' ▸ hpW, hcover⟩
    · intro z hz
      rcases hfront hz with hzloop | hzline
      · exact Or.inl hzloop
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hzline
        exact Or.inr (mem_iUnion.mpr ⟨lines i,
          mem_iUnion.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩⟩)
    · intro l hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact hlines i

end PoincareConjecture
