import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallSphereCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceChart

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_reference_cap_corrected_chart
    (A : BallNeighborhoodChart E3 E3)
    (C : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hC : ContDiffOn ℝ ∞ C C.source)
    (hCi : ContDiffOn ℝ ∞ C.symm C.target)
    (a ε b : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (hε : 0 < ε) (hb : 0 < b)
    (hzero : closedBall (0 : E2) (1 + ε) ×ˢ ({0} : Set ℝ) ⊆ C.source)
    (hcentral : ∀ X : E2, ‖X‖ ≤ 1 + ε →
      C (X, 0) = A.chart (referenceCapPoint a X))
    (hpositive : ∀ X : E2, ‖X‖ ≤ 1 + ε → ∀ s : ℝ,
      0 < s → s < b → C (X, s) ∈ A.closedRegionᶜ)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (c₂ : ℝ) (hc₂ : c₂ ∈ Ioo (1 / 2 : ℝ) a)
    (heq : ∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z)) :
    let G0 := heightCoordinates.toDiffeomorph.trans
      (referenceFlatteningDiffeomorph a ha α hα hpos)
    let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
    ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      (∀ y ∈ sphere (0 : E3) 1, F y = y) ∧
      F '' ball (0 : E3) 1 = ball 0 1 ∧
      F '' closedBall (0 : E3) 1 = closedBall 0 1 ∧
      (∀ᶠ y in 𝓝ˢ Da, F y = referenceCapTransition A C a ha α hα hpos y) ∧
      (∃ L : Set E3, IsCompact L ∧ ∀ y, y ∉ L → F y = y) ∧
      ∃ A' : BallNeighborhoodChart E3 E3,
        A'.chart = F.toHomeomorph.toOpenPartialHomeomorph.trans A.chart ∧
        A'.chart.source = F ⁻¹' A.chart.source ∧
        A'.chart.target = A.chart.target ∧
        (∀ y : E3, A'.chart y = A.chart (F y)) ∧
        (∀ Y : E3, A'.chart.symm Y = F.symm (A.chart.symm Y)) ∧
        A'.inside = A.inside ∧ A'.closedRegion = A.closedRegion ∧
        A'.boundary = A.boundary ∧
        (∀ y ∈ sphere (0 : E3) 1, A'.chart y = A.chart y) ∧
        (∀ᶠ y in 𝓝ˢ Da, y ∈ A'.chart.source ∧ G0 y ∈ C.source ∧
          A'.chart y = C (G0 y)) ∧
        ∀ (η : ℝ) (_hη : 0 < η)
          (f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞),
          (∀ z : ℝ, |z| ≤ η / 8 → f z = z) →
          ∀ B : BallNeighborhoodChart E3 E3,
            B.chart =
              (referenceCompressedDiffeomorph
                a ha α hα hpos f).toHomeomorph.toOpenPartialHomeomorph.trans C →
            ∀ᶠ y in 𝓝ˢ Da,
              y ∈ A'.chart.source ∧ y ∈ B.chart.source ∧ A'.chart y = B.chart y := by
  let G0 := heightCoordinates.toDiffeomorph.trans
    (referenceFlatteningDiffeomorph a ha α hα hpos)
  let Da := {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2}
  let T := referenceCapTransition A C a ha α hα hpos
  let U := T.source ∩ {y : E3 |
    c₂ < (heightCoordinates y).2 ∧ ‖(G0 y).1‖ < 1 + ε ∧ |(G0 y).2| < b}
  obtain ⟨hTs, _, hTf, _, hT, _⟩ := referenceCapTransition_spec A C hC hCi a ha α hα hpos
  obtain ⟨hU, hDaU, hfixed, _, hn⟩ := referenceCapTransition_oriented_patch
    A C hC hCi a ε b ha hε hb hzero hcentral hpositive α hα hpos c₂ hc₂ heq
  have hDaeq : Da = sphere (0 : E3) 1 ∩ {y : E3 | a ≤ (heightCoordinates y).2} := by
    ext y
    simp only [Da, mem_inter_iff, mem_ofPred_eq, mem_sphere_zero_iff_norm]
  have hDa : IsCompact Da := by
    rw [hDaeq]
    exact (isCompact_sphere (0 : E3) 1).inter_right
      (isClosed_le continuous_const heightCoordinates.continuous.snd)
  have hDaS : Da ⊆ sphere (0 : E3) 1 := fun y hy => mem_sphere_zero_iff_norm.mpr hy.1
  obtain ⟨F, hFfixed, hFball, hFclosed, hFnear, hFsupport⟩ :=
    exists_sphere_fixed_patch_extension T hDa hDaS hU hDaU
      (hT.mono inter_subset_left) hfixed hn
  let e := F.toHomeomorph.toOpenPartialHomeomorph.trans A.chart
  have hesource : closedBall (0 : E3) 1 ⊆ e.source := by
    intro y hy
    refine ⟨mem_univ _, A.closedBall_subset_source ?_⟩
    rw [← hFclosed]
    exact ⟨y, hy, rfl⟩
  have he : ContDiffOn ℝ ∞ e e.source :=
    A.smooth.comp F.contMDiff_toFun.contDiff.contDiffOn (fun _ hy => hy.2)
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    F.contMDiff_invFun.contDiff.comp_contDiffOn (A.smooth_symm.mono inter_subset_left)
  let A' : BallNeighborhoodChart E3 E3 := {
    chart := e
    closedBall_subset_source := hesource
    smooth := he
    smooth_symm := hei }
  have hAsource : A'.chart.source = F ⁻¹' A.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ F y ∈ A.chart.source) ↔ F y ∈ A.chart.source
    simp only [mem_univ, true_and]
  have hAtarget : A'.chart.target = A.chart.target := by
    ext Y
    change (Y ∈ A.chart.target ∧ A.chart.symm Y ∈ (univ : Set E3)) ↔ Y ∈ A.chart.target
    simp only [mem_univ, and_true]
  have hAf (y : E3) : A'.chart y = A.chart (F y) := rfl
  have hAi (Y : E3) : A'.chart.symm Y = F.symm (A.chart.symm Y) := rfl
  have hinside : A'.inside = A.inside := by
    change (fun y => A.chart (F y)) '' ball (0 : E3) 1 = A.chart '' ball (0 : E3) 1
    rw [← image_image, hFball]
  have hclosed : A'.closedRegion = A.closedRegion := by
    change (fun y => A.chart (F y)) '' closedBall (0 : E3) 1 =
      A.chart '' closedBall (0 : E3) 1
    rw [← image_image, hFclosed]
  have hpointwise (y : E3) (hy : y ∈ sphere (0 : E3) 1) : A'.chart y = A.chart y := by
    rw [hAf, hFfixed y hy]
  have hboundary : A'.boundary = A.boundary := image_congr hpointwise
  have hTsnear : ∀ᶠ y in 𝓝ˢ Da, y ∈ T.source :=
    T.open_source.mem_nhdsSet.mpr (fun y hy => (hDaU hy).1)
  have hgerm : ∀ᶠ y in 𝓝ˢ Da,
      y ∈ A'.chart.source ∧ G0 y ∈ C.source ∧ A'.chart y = C (G0 y) := by
    filter_upwards [hFnear, hTsnear] with y hFy hyt
    have hactual : G0 y ∈ C.source ∧ C (G0 y) ∈ A.chart.target := by
      rwa [hTs] at hyt
    refine ⟨?_, hactual.1, ?_⟩
    · rw [hAsource]
      change F y ∈ A.chart.source
      rw [hFy, hTf]
      exact A.chart.map_target hactual.2
    · rw [hAf, hFy, hTf, A.chart.right_inv hactual.2]
  refine ⟨F, hFfixed, hFball, hFclosed, hFnear, hFsupport, A', rfl,
    hAsource, hAtarget, hAf, hAi, hinside, hclosed, hboundary, hpointwise, hgerm, ?_⟩
  intro η hη f hf B hB
  have hcompression := (referenceCompressedDiffeomorph_cap_germ a ha α hα hpos
    c₂ hc₂.2 heq η hη f hf).2
  have hBnear : ∀ᶠ y in 𝓝ˢ Da, y ∈ B.chart.source :=
    B.chart.open_source.mem_nhdsSet.mpr (fun y hy =>
      B.closedBall_subset_source (mem_closedBall_zero_iff.mpr hy.1.le))
  filter_upwards [hgerm, hcompression, hBnear] with y hy heqy hBy
  refine ⟨hy.1, hBy, ?_⟩
  rw [hy.2.2, hB]
  change C (G0 y) = C (referenceCompressedDiffeomorph a ha α hα hpos f y)
  exact congrArg C heqy.symm

end PoincareConjecture.M25.Topology3D
