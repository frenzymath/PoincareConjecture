import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCornerTopology
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerChart














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture





theorem m64Intrinsic_exists_loop_corner_chart
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates)) :
    ∃ H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ H.source ∧ H 0 = gamma 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target ∧
      (∀ s : ℝ, H !₂[s, 0] = gamma s) ∧
      (∀ s : ℝ, H !₂[0, s] = gamma (T - s)) ∧
      (∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ gamma '' Icc 0 T ↔
        (z 0 = 0 ∧ 0 ≤ z 1) ∨ (0 ≤ z 0 ∧ z 1 = 0)) ∧
      mfderiv (𝓡 2) (𝓡 2) H 0 !₂[1, 0] = deriv gamma 0 ∧
      mfderiv (𝓡 2) (𝓡 2) H 0 !₂[0, 1] = -deriv gamma T := by
  let beta : ℝ → AnnulusCoordinates := fun s => gamma (T - s)
  have hbeta : ContDiff ℝ ∞ beta := hg.comp (contDiff_const.sub contDiff_id)
  have hbetaD : HasDerivAt beta (-deriv gamma T) 0 := by
    have hd : HasDerivAt gamma (deriv gamma T) (T - (0 : ℝ)) := by
      simpa using (hg.differentiable (by simp) T).hasDerivAt
    simpa [beta, Function.comp_def] using!
      (hd.scomp 0
        ((hasDerivAt_const (0 : ℝ) T).sub (hasDerivAt_id (0 : ℝ))))
  have hind' : LinearIndependent ℝ
      (![deriv gamma 0, deriv beta 0] : Fin 2 → AnnulusCoordinates) := by
    rw [hbetaD.deriv]
    exact hind
  obtain ⟨H, h0, hbase, hH, hHi, haxis, haxis', hD, hD'⟩ :=
    m64Intrinsic_exists_two_arc_corner_chart isOpen_univ isOpen_univ
      (mem_univ 0) (mem_univ 0) hg.contDiffOn hbeta.contDiffOn
      (by simpa only [beta, sub_zero] using hend.symm) hind'
  obtain ⟨a, W, ha, hia, hib, hW, hpW, hcover⟩ :=
    m64Intrinsic_loop_corner_decomposition hg.continuous hT hend hinj
  let c := rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)
  have hc0 : c 0 = (0 : AnnulusCoordinates) := by
    ext i
    fin_cases i <;> rfl
  have hline₁ (s : ℝ) : AffineMap.lineMap (c 0) (c 1) s = !₂[s, 0] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hline₂ (s : ℝ) : AffineMap.lineMap (c 0) (c 2) s = !₂[0, s] := by
    ext i
    fin_cases i <;> simp [c, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  have hrays := m64Intrinsic_two_arc_frontier_germ H c (hc0 ▸ h0) ha ha
    hg.continuous.continuousOn hbeta.continuous.continuousOn hia hib
      (fun s => by rw [hline₁]; exact haxis s)
      (fun s => by rw [hline₂]; exact haxis' s) hW
      (by rwa [hc0, hbase]) hcover
  refine ⟨H, h0, hbase, hH, hHi, haxis, haxis', ?_, hD, ?_⟩
  · simpa [hc0, c, rightTriangleBasis_coord] using hrays
  · simpa only [hbetaD.deriv] using hD'





theorem m64Intrinsic_exists_loop_corner_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ H : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (0 : AnnulusCoordinates) ∈ H.source ∧ H 0 = gamma 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H H.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ H.symm H.target ∧
      (∀ s : ℝ, H !₂[s, 0] = gamma s) ∧
      (∀ s : ℝ, H !₂[0, s] = gamma (T - s)) ∧
      ((∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ 0 ≤ z 0 ∧ 0 ≤ z 1) ∨
        (∀ᶠ z in 𝓝 (0 : AnnulusCoordinates), H z ∈ closure U ↔ z 0 ≤ 0 ∨ z 1 ≤ 0)) := by
  obtain ⟨H, h0, hbase, hH, hHi, haxis, haxis', hrays, _, _⟩ :=
    m64Intrinsic_exists_loop_corner_chart hg hT hend hinj hind
  let c := rightTriangleBasis (show (0 : ℝ) < 1 by norm_num)
  have hc0 : c 0 = (0 : AnnulusCoordinates) := by ext i; fin_cases i <;> rfl
  have hfront : H (c 0) ∈ frontier U := by
    rw [hc0, hbase, hfU]
    exact ⟨0, ⟨le_rfl, hT.le⟩, rfl⟩
  have hrays' : ∀ᶠ z in 𝓝 (c 0), H z ∈ frontier U ↔
      (c.coord 1 z = 0 ∧ 0 ≤ c.coord 2 z) ∨
        (0 ≤ c.coord 1 z ∧ c.coord 2 z = 0) := by
    simpa [hc0, hfU, c, rightTriangleBasis_coord] using hrays
  have hside := m64Intrinsic_jordan_corner_germ hU hV hdisj (hfU.trans hfV.symm)
    H c (hc0 ▸ h0) hfront hrays'
  refine ⟨H, h0, hbase, hH, hHi, haxis, haxis', ?_⟩
  simpa [hc0, c, rightTriangleBasis_coord] using hside

end PoincareConjecture
