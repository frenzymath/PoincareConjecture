import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcFrontierGerm
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle Matrix
open Poincare.Topology.Plane.Triangles PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_two_arc_corner_coordinates
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha 0 ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ W)
    (hfV : frontier V = frontier U) :
    ∃ (phi : AnnulusCoordinates → ℝ × ℝ)
      (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (positive : Bool),
      HasFDerivAt phi L.toContinuousLinearMap (alpha 0) ∧ phi (alpha 0) = 0 ∧
      L.symm (1, 0) = deriv alpha 0 ∧ L.symm (0, 1) = deriv beta 0 ∧
      (∀ᶠ z in 𝓝 (alpha 0), z ∈ closure U ↔
        if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
        else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) := by
  obtain ⟨H, h0, hHbase, hH, hHi, haxis, haxis', hu, hv⟩ :=
    m64Intrinsic_exists_two_arc_corner_chart isOpen_univ isOpen_univ
      (mem_univ 0) (mem_univ 0) ha.contDiffOn hb.contDiffOn hbase hind
  let c := rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)
  have hc0 : c 0 = (0 : AnnulusCoordinates) := by ext i; fin_cases i <;> rfl
  have hline0 (s : ℝ) : AffineMap.lineMap (c 0) (c 1) s = !₂[s, 0] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hline1 (s : ℝ) : AffineMap.lineMap (c 0) (c 2) s = !₂[0, s] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hrays := m64Intrinsic_two_arc_frontier_germ H c (hc0 ▸ h0) hA hB
    ha.continuous.continuousOn hb.continuous.continuousOn hai hbi
    (fun s => by rw [hline0]; exact haxis s)
    (fun s => by rw [hline1]; exact haxis' s) hW
    (by simpa only [hc0, hHbase] using hpW) hfU
  have hfront : H (c 0) ∈ frontier U := by
    rw [hc0, hHbase, hfU]
    exact Or.inl (Or.inl ⟨0, ⟨le_rfl, hA.le⟩, rfl⟩)
  have hside := m64Intrinsic_jordan_corner_germ hU hV hdisj hfV.symm
    H c (hc0 ▸ h0) hfront hrays
  have hD : H.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hH.mdifferentiableOn (by simp), hHi.mdifferentiableOn (by simp)⟩
  let J : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates := hD.mfderiv h0
  let L := J.symm.trans collarParameterEquiv
  let phi := collarParameterEquiv ∘ H.symm
  have hd : HasFDerivAt H J.toContinuousLinearMap 0 := by
    change HasFDerivAt H (mfderiv (𝓡 2) (𝓡 2) H 0) 0
    rw [mfderiv_eq_fderiv]
    exact ((contMDiffOn_iff_contDiffOn.mp hH 0 h0).contDiffAt
      (H.open_source.mem_nhds h0)).differentiableAt (by simp) |>.hasFDerivAt
  have htarget : alpha 0 ∈ H.target := hHbase ▸ H.map_source h0
  have hzero : H.symm (alpha 0) = 0 := by rw [← hHbase, H.left_inv h0]
  have hdi : HasFDerivAt H.symm J.symm.toContinuousLinearMap (alpha 0) := by
    apply H.hasFDerivAt_symm htarget
    simpa only [hzero] using hd
  have hphi : HasFDerivAt phi L.toContinuousLinearMap (alpha 0) :=
    collarParameterEquiv.hasFDerivAt.comp (alpha 0) hdi
  obtain ⟨positive, hside'⟩ : ∃ positive : Bool,
      ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔
        if positive then 0 ≤ z 0 ∧ 0 ≤ z 1 else z 0 ≤ 0 ∨ z 1 ≤ 0 := by
    rcases hside with hs | hs
    · exact ⟨true, by simpa [hc0, c, rightTriangleBasis_coord] using hs⟩
    · exact ⟨false, by simpa [hc0, c, rightTriangleBasis_coord] using hs⟩
  refine ⟨phi, L, positive, hphi, ?_, ?_, ?_, ?_⟩
  · simp only [phi, Function.comp_apply, hzero, map_zero]
  · exact hu
  · exact hv
  · have ht : Tendsto H.symm (𝓝 (alpha 0)) (𝓝 (0 : AnnulusCoordinates)) := by
      simpa only [hzero] using (H.symm.continuousAt htarget).tendsto
    filter_upwards [ht.eventually hside', H.open_target.mem_nhds htarget] with z hz hzt
    rw [H.right_inv hzt] at hz
    exact hz

end PoincareConjecture
