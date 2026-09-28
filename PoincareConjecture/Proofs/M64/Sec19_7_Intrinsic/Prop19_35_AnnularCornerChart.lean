import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExactTwoArcCorner
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerAnnularSide

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_annular_corner_chart
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U)
    (hnorm : ‖alpha 0‖ = 1) (hinward : 0 < inner ℝ (alpha 0) (deriv beta 0))
    (hsub : closure U ⊆ standardAnnulusDomain) :
    ∃ H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ H.source ∧ H 0 = alpha 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target ∧
      (∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ 0 ≤ z 0 ∧ 0 ≤ z 1) := by
  obtain ⟨H, h0, hHbase, _, hH, hHi, _, haxis, _, hside⟩ :=
    m64Intrinsic_exists_exact_two_arc_corner_region ha hb hA hB hai hbi hbase hind
      hW hpW hU hV hdisj hfU hfV isOpen_univ (mem_univ _)
  have hD : H.MDifferentiable 𝓘(ℝ, ℝ × ℝ) (𝓡 2) :=
    ⟨hH.contMDiffOn.mdifferentiableOn (by simp),
      hHi.contMDiffOn.mdifferentiableOn (by simp)⟩
  let J : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates := hD.mfderiv h0
  have hd : HasFDerivAt H J.toContinuousLinearMap 0 := by
    change HasFDerivAt H (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) H 0) 0
    rw [mfderiv_eq_fderiv]
    exact ((hH 0 h0).contDiffAt (H.open_source.mem_nhds h0)).differentiableAt
      (by simp) |>.hasFDerivAt
  have htarget : alpha 0 ∈ H.target := hHbase ▸ H.map_source h0
  have hzero : H.symm (alpha 0) = 0 := by rw [← hHbase, H.left_inv h0]
  have hdi : HasFDerivAt H.symm J.symm.toContinuousLinearMap (alpha 0) := by
    apply H.hasFDerivAt_symm htarget
    simpa only [hzero] using hd
  have hv : J (0, 1) = deriv beta 0 := by
    have hp : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) (0, 1) 0 :=
      (hasDerivAt_const 0 (0 : ℝ)).prodMk (hasDerivAt_id 0)
    have hh := hd.comp_hasDerivAt (f := fun s : ℝ => ((0 : ℝ), s)) 0 hp
    change HasDerivAt (fun s : ℝ => H (0, s)) (J (0, 1)) 0 at hh
    rw [show (fun s : ℝ => H (0, s)) = beta from funext haxis] at hh
    exact hh.deriv.symm
  obtain ⟨positive, hregion⟩ : ∃ positive : Bool, ∀ z ∈ H.source,
      H z ∈ closure U ↔ if positive then 0 ≤ z.1 ∧ 0 ≤ z.2
        else z.1 ≤ 0 ∨ z.2 ≤ 0 := by
    rcases hside with hs | hs
    · exact ⟨true, hs⟩
    · exact ⟨false, hs⟩
  have hinverse : ∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔
      if positive then 0 ≤ (H.symm z).1 ∧ 0 ≤ (H.symm z).2
      else (H.symm z).1 ≤ 0 ∨ (H.symm z).2 ≤ 0 := by
    filter_upwards [H.open_target.mem_nhds htarget] with z hz
    simpa only [H.right_inv hz] using hregion (H.symm z) (H.map_target hz)
  have hpositive := m64Intrinsic_annular_corner_is_convex hnorm J.symm hdi hzero
    (by simpa only [ContinuousLinearEquiv.symm_symm, hv] using hinward)
    hsub positive hinverse
  let e := collarParameterEquiv
  let F := e.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hF0 : (0 : AnnulusCoordinates) ∈ F.source :=
    ⟨mem_univ _, by change e 0 ∈ H.source; simpa only [map_zero] using h0⟩
  have hF : ContDiffOn ℝ ∞ F F.source :=
    hH.comp e.contDiff.contDiffOn (fun _ hz => hz.2)
  have hFi : ContDiffOn ℝ ∞ F.symm F.target :=
    e.symm.contDiff.comp_contDiffOn (hHi.mono (fun _ hz => hz.1))
  refine ⟨F, hF0, ?_, contMDiffOn_iff_contDiffOn.mpr hF,
    contMDiffOn_iff_contDiffOn.mpr hFi, ?_⟩
  · change H (e 0) = alpha 0
    rw [map_zero, hHbase]
  · filter_upwards [F.open_source.mem_nhds hF0] with z hz
    have hh := hregion (e z) hz.2
    change H (e z) ∈ closure U ↔ 0 ≤ z 0 ∧ 0 ≤ z 1
    simpa [e, collarParameterEquiv, hpositive] using hh

end PoincareConjecture
