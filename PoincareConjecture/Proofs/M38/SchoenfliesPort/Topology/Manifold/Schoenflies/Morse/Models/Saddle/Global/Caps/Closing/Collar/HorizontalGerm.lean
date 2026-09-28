import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalTransport
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.CapGerm

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_horizontal_zero_section_chart
    (D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
    (A : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDn : ∀ z ∈ D.source, ‖A.symm (D z)‖ = 1 + z.2) :
    ∃ m : OpenPartialHomeomorph E2 S2,
      m.source = {y | (y, (0 : Real)) ∈ D.source} ∧
      ∀ y ∈ m.source, A (m y) = D (y, 0) := by
  let B : E2 → E3 := fun y => A.symm (D (y, 0))
  let k : E2 → S2 := sphereProjection ∘ B
  let l : S2 → E2 := fun q => (D.symm (A q)).1
  let V : Set E2 := {y | (y, (0 : Real)) ∈ D.source}
  let W : Set S2 := {q | A q ∈ D.target}
  have hV : IsOpen V := D.open_source.preimage (continuous_id.prodMk continuous_const)
  have hW : IsOpen W := D.open_target.preimage (A.continuous.comp continuous_subtype_val)
  have hBnorm (y : E2) (hy : y ∈ V) : ‖B y‖ = 1 := by
    simpa only [add_zero] using hDn (y, 0) hy
  have hkcoe (y : E2) (hy : y ∈ V) : (k y : E3) = B y := by
    rw [show k y = sphereProjection (B y) from rfl,
      sphereProjection_coe (norm_ne_zero_iff.mp (by rw [hBnorm y hy]; norm_num)),
      hBnorm y hy, inv_one, one_smul]
  have hAk (y : E2) (hy : y ∈ V) : A (k y) = D (y, 0) := by
    rw [hkcoe y hy]
    exact A.apply_symm_apply _
  have hlnormal (q : S2) (hq : q ∈ W) : (D.symm (A q)).2 = 0 := by
    have hinv : D (D.symm (A q)) = A q := D.right_inv hq
    have hh := hDn (D.symm (A q)) (D.map_target hq)
    rw [hinv, A.symm_apply_apply, norm_eq_of_mem_sphere q] at hh
    linarith
  have hlpair (q : S2) (hq : q ∈ W) : (l q, 0) = D.symm (A q) :=
    Prod.ext rfl (hlnormal q hq).symm
  have hkmap : MapsTo k V W := fun y hy => by
    change A (k y) ∈ D.target
    rw [hAk y hy]
    exact D.map_source hy
  have hlmap : MapsTo l W V := fun q hq => by
    change (l q, 0) ∈ D.source
    rw [hlpair q hq]
    exact D.map_target hq
  have hleft (y : E2) (hy : y ∈ V) : l (k y) = y := by
    change (D.symm (A (k y))).1 = y
    rw [hAk y hy]
    have hi : D.symm (D (y, 0)) = (y, 0) := D.left_inv hy
    rw [hi]
  have hright (q : S2) (hq : q ∈ W) : k (l q) = q := by
    apply Subtype.ext
    rw [hkcoe _ (hlmap hq)]
    change A.symm (D (l q, 0)) = q
    rw [hlpair q hq]
    have hi : D (D.symm (A q)) = A q := D.right_inv hq
    rw [hi, A.symm_apply_apply]
  have hk : ContinuousOn k V := by
    intro y hy
    have hd := D.contMDiffOn_toFun.contDiffOn.contDiffAt (D.open_source.mem_nhds hy)
    have hB := A.symm.contMDiff.contMDiffAt.contDiffAt.comp y
      (hd.comp y (contDiffAt_id.prodMk contDiffAt_const))
    change ContDiffAt Real ∞ B y at hB
    exact ((contMDiffAt_sphereProjection
      (norm_ne_zero_iff.mp (by rw [hBnorm y hy]; norm_num))).continuousAt.comp
        hB.continuousAt).continuousWithinAt
  have hl : ContinuousOn l W := continuous_fst.comp_continuousOn
    (D.symm.toOpenPartialHomeomorph.continuousOn.comp
      (A.continuous.comp continuous_subtype_val).continuousOn (fun q hq => hq))
  let m : OpenPartialHomeomorph E2 S2 :=
    { toPartialEquiv :=
        { toFun := k
          invFun := l
          source := V
          target := W
          map_source' := hkmap
          map_target' := hlmap
          left_inv' := hleft
          right_inv' := hright }
      open_source := hV
      open_target := hW
      continuousOn_toFun := hk
      continuousOn_invFun := hl }
  exact ⟨m, rfl, hAk⟩

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_surface_germ_of_horizontal_collar_matching
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (H G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3)
    (D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
    (hDn : ∀ z ∈ D.source,
      ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 + z.2)
    (hDq : ∀ q ∈ sphere (0 : E2) 1,
      D (q, 0) = data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q))
    (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hTs : T.source ⊆ (data.actualDisk i).source)
    {O : Set E2} (hO : IsOpen O) (hcO : sphere (0 : E2) 1 ⊆ O)
    (hOT : O ⊆ T.target) (hOD : ∀ y ∈ O, (y, 0) ∈ D.source)
    (hmatch : ∀ y ∈ O,
      G (actualCapPhysicalCoordinates data H i (T.symm y)) = D (y, 0)) :
    ∃ U : Set E3, IsOpen U ∧
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
        (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))) ∩ U =
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
  obtain ⟨m, hms, hm⟩ := exists_horizontal_zero_section_chart D
    data.toTerminalSaddleGeometry.filledModel hDn
  let s : S2 → E3 := G ∘ data.toTerminalSaddleGeometry.flatten.symm ∘
    H ∘ data.toTerminalSaddleGeometry.flatten ∘ g
  let t : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
  let n := T.toOpenPartialHomeomorph.symm.trans (data.actualDisk i)
  have hs : Topology.IsEmbedding s := G.toHomeomorph.isEmbedding.comp
    (data.toTerminalSaddleGeometry.flatten.symm.toHomeomorph.isEmbedding.comp
      (H.toHomeomorph.isEmbedding.comp
        (data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
          (M.tree.embedding_of_mem_leaves hg).isEmbedding)))
  have ht : Topology.IsEmbedding t :=
    data.toTerminalSaddleGeometry.filledModel.toHomeomorph.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have hOn : O ⊆ n.source := fun y hy => ⟨hOT hy, hTs (T.map_target (hOT hy))⟩
  have hOm : O ⊆ m.source := by rw [hms]; exact hOD
  have heq : EqOn (s ∘ n) (t ∘ m) O := by
    intro y hy
    change G (data.toTerminalSaddleGeometry.flatten.symm
      (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i (T.symm y)))))) = _
    rw [← actualCapPhysicalCoordinates_eq, hmatch y hy]
    exact (hm y (hOm hy)).symm
  obtain ⟨U, hU, hOU, hsurface⟩ := exists_common_surface_neighborhood_of_eqOn_charts
    hs ht n m hO hOn hOm heq
  refine ⟨U, hU, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hh := hOU (mem_image_of_mem (s ∘ n) (hcO hy))
    rw [heq (hcO hy)] at hh
    change data.toTerminalSaddleGeometry.filledModel (m y) ∈ U at hh
    rw [hm y (hOm (hcO hy)), hDq y hy] at hh
    exact hh
  · have hsr : range s = G '' (data.toTerminalSaddleGeometry.flatten.symm ''
        (H '' (data.toTerminalSaddleGeometry.flatten '' range g))) := by
      simp only [s, range_comp]
    have htr : range t = data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1 := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        exact mem_image_of_mem _ q.property
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rwa [hsr, htr] at hsurface

theorem exists_relative_horizontal_terminal_surface_germ_within
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
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ N) :
    ∃ (S U : Set E3), IsCompact S ∧ S ⊆ N ∧ IsOpen U ∧
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
          (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
  obtain ⟨c, D, T, O, S, _, _, hDq, hDh, _, _, hTs, hO, hcO, _, hOT, hOD,
      hS, hSN, _, G, hfix, hheight, hband, hmap⟩ :=
    exists_relative_horizontal_terminal_collar_transport_within
      data hg Φ χ H hH hχ hplanar hlabels i hN hcircleN
  obtain ⟨U, hU, hcU, heq⟩ := terminal_surface_germ_of_horizontal_collar_matching
    data hg H G i D (fun z hz => (hDh z hz).2) hDq T hTs hO hcO
      (subset_closure.trans hOT) (fun y hy => hOD y (subset_closure hy))
      (fun y hy => hmap y (subset_closure hy))
  exact ⟨S, U, hS, hSN, hU, hcU, G, hfix, hheight, hband, heq⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
