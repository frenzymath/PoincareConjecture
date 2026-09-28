import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.TerminalGraph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.RadialTransport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_relative_terminal_collar_transport_within
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) {N : Set E3} (hN : IsOpen N)
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y))) ''
        sphere (0 : E2) 1 ⊆ N) :
    ∃ (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (O : Set E2) (S : Set E3),
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      T.target ⊆ (data.modelDisk i).source ∧
      IsOpen O ∧ sphere (0 : E2) 1 ⊆ O ∧
      IsCompact (closure O) ∧ closure O ⊆ T.target ∧ IsCompact S ∧ S ⊆ N ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ y ∈ closure O,
          G (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i (T.symm y))))) =
            data.toTerminalSaddleGeometry.flatten
              (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) := by
  obtain ⟨T, a, hTc, hTi, hTs, hTm, ha, haCircle, hgraph, _, V, hV, hcV, hVT, hazero⟩ :=
    exists_actual_terminal_radial_graph data hg Φ χ H hH hχ hplanar hlabels i
  let A := data.toTerminalSaddleGeometry.filledModel.trans data.toTerminalSaddleGeometry.flatten
  let q : E2 × Real → E3 := fun z => A ((1 + (1 - z.2) * a z.1) •
    (data.modelDisk i z.1 : E3))
  have hm : ContinuousOn (fun y => (data.modelDisk i y : E3)) V :=
    (contMDiff_coe_sphere.comp_contMDiffOn (data.modelDisk_smooth i)).continuousOn.mono
      (hVT.trans hTm)
  have hq : ContinuousOn q (V ×ˢ (univ : Set Real)) :=
    A.contMDiff.continuous.comp_continuousOn
      ((continuousOn_const.add ((continuousOn_const.sub continuousOn_snd).mul
        (ha.continuousOn.comp continuousOn_fst (fun _ hz => hVT hz.1)))).smul
        (hm.comp continuousOn_fst (fun _ hz => hz.1)))
  have hqopen : IsOpen ((V ×ˢ (univ : Set Real)) ∩ q ⁻¹' N) :=
    hq.isOpen_inter_preimage (hV.prod isOpen_univ) hN
  have hqcircle : sphere (0 : E2) 1 ×ˢ Icc (0 : Real) 1 ⊆
      (V ×ˢ (univ : Set Real)) ∩ q ⁻¹' N := by
    rintro ⟨y, t⟩ ⟨hy, _⟩
    refine ⟨⟨hcV hy, mem_univ _⟩, ?_⟩
    change A ((1 + (1 - t) * a y) • (data.modelDisk i y : E3)) ∈ N
    rw [haCircle hy, mul_zero, add_zero, one_smul]
    exact hcircleN (mem_image_of_mem _ hy)
  obtain ⟨U, J, hU, _, hcU, hIJ, hUJ⟩ := generalized_tube_lemma
    (isCompact_sphere (0 : E2) 1) isCompact_Icc hqopen hqcircle
  obtain ⟨O, hO, hcO, hOV⟩ := (isCompact_sphere (0 : E2) 1).exists_isOpen_closure_subset
    (((hV.inter hU).inter isOpen_ball).mem_nhdsSet.mpr
      (subset_inter (subset_inter hcV hcU) (sphere_subset_closedBall.trans
        (closedBall_subset_ball (by norm_num : (1 : Real) < 2)))))
  have hOVbase : closure O ⊆ V := fun y hy => (hOV hy).1.1
  have hOc : IsCompact (closure O) := (isCompact_closedBall (0 : E2) 2).of_isClosed_subset
    isClosed_closure (fun x hx => ball_subset_closedBall (hOV hx).2)
  let W : Set E3 := A.symm '' data.toTerminalSaddleGeometry.modelBand
  have hWsphere : W ⊆ sphere (0 : E3) 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hwhole : data.toTerminalSaddleGeometry.modelBand ⊆
        A '' sphere (0 : E3) 1 := by
      change data.toTerminalSaddleGeometry.modelBand ⊆
        (data.toTerminalSaddleGeometry.flatten ∘ data.toTerminalSaddleGeometry.filledModel) '' _
      have hd := data.model_decomposition
      rw [image_image] at hd
      exact hd.symm ▸ subset_union_left
    obtain ⟨x, hx, rfl⟩ := hwhole hz
    simpa only [A.symm_apply_apply] using hx
  have hzero (y : E2) (hy : y ∈ V) (hw : (data.modelDisk i y : E3) ∈ W) : a y = 0 := by
    apply hazero y hy
    obtain ⟨z, hz, heq⟩ := hw
    have hh := congrArg A heq
    simp only [A.apply_symm_apply] at hh
    exact hh ▸ hz
  have hsweep : ∀ t ∈ Icc (0 : Real) 1, ∀ y ∈ closure O,
      (1 + (1 - t) * a y) • (data.modelDisk i y : E3) ∈ A ⁻¹' N := by
    intro t ht y hy
    have hh := hUJ (show (y, t) ∈ U ×ˢ J from ⟨(hOV hy).1.2, hIJ ht⟩)
    exact hh.2
  obtain ⟨S, hS, hSN, _, G, hGfix, hGW, hGmap⟩ := exists_supported_radial_graph_flattening_within
    (data.modelDisk i) (data.modelDisk_smooth i) (data.modelDisk_symm_smooth i)
    a hV (hVT.trans hTm) (ha.mono hVT) (fun y hy => (hgraph y (hVT hy)).1)
    hOc hOVbase hWsphere hzero (U := A ⁻¹' N) (hN.preimage A.contMDiff.continuous) hsweep
  let G' := A.symm.trans (G.trans A)
  refine ⟨T, O, A '' S, hTc, hTi, hTs, hTm, hO, hcO, hOc,
    hOVbase.trans hVT, hS.image A.contMDiff.continuous, ?_, G', ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hSN hz
  · intro z hz
    have hnot : A.symm z ∉ S := by
      intro hs
      exact hz ⟨A.symm z, hs, A.apply_symm_apply z⟩
    change A (G (A.symm z)) = z
    rw [hGfix _ hnot, A.apply_symm_apply]
  · intro z hz
    change A (G (A.symm z)) = z
    rw [hGW (mem_image_of_mem A.symm hz), id_eq, A.apply_symm_apply]
  · intro y hy
    have h := hGmap y hy
    rw [← (hgraph y (hVT (hOVbase hy))).2] at h
    have hh := congrArg A h
    exact hh

theorem exists_relative_terminal_collar_transport
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) :
    ∃ (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (O : Set E2) (S : Set E3),
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      T.target ⊆ (data.modelDisk i).source ∧
      IsOpen O ∧ sphere (0 : E2) 1 ⊆ O ∧
      IsCompact (closure O) ∧ closure O ⊆ T.target ∧ IsCompact S ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
        ∀ y ∈ closure O,
          G (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i (T.symm y))))) =
            data.toTerminalSaddleGeometry.flatten
              (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) := by
  obtain ⟨T, O, S, hTc, hTi, hTs, hTm, hO, hcO, hOc, hOT, hS, _, G, hfix, hband, hmap⟩ :=
    exists_relative_terminal_collar_transport_within data hg Φ χ H hH hχ hplanar hlabels i
      isOpen_univ (subset_univ _)
  exact ⟨T, O, S, hTc, hTi, hTs, hTm, hO, hcO, hOc, hOT, hS, G, hfix, hband, hmap⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
