import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.TerminalProjection



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




theorem exists_actual_terminal_radial_graph
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
    ∃ (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (a : E2 → Real),
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      T.target ⊆ (data.modelDisk i).source ∧
      ContDiffOn Real ∞ a T.target ∧
      EqOn a (fun _ => 0) (sphere (0 : E2) 1) ∧
      (∀ y ∈ T.target, -1 < a y ∧
        actualCapModelCoordinates data H i (T.symm y) =
          (1 + a y) • (data.modelDisk i y : E3)) ∧
      (∀ y ∈ T.target, actualCapModelCoordinates data H i (T.symm y) ∈
        sphere (0 : E3) 1 → a y = 0) ∧
      ∃ V : Set E2, IsOpen V ∧ sphere (0 : E2) 1 ⊆ V ∧ V ⊆ T.target ∧
        ∀ y ∈ V, data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈
            data.toTerminalSaddleGeometry.modelBand → a y = 0 := by
  obtain ⟨T, hTc, hTi, hTs, hT⟩ :=
    exists_actual_terminal_projection_chart data hg Φ χ H hH hχ hplanar hlabels i
  let F := actualCapModelCoordinates data H i
  let a : E2 → Real := fun y => ‖F (T.symm y)‖ - 1
  have hnonzero (y : E2) (hy : y ∈ T.target) : F (T.symm y) ≠ 0 :=
    (hT _ (T.map_target hy)).1
  have hproj (y : E2) (hy : y ∈ T.target) :
      data.modelDisk i y = sphereProjection (F (T.symm y)) := by
    have heq := (hT _ (T.map_target hy)).2.2
    simp only [T.right_inv hy] at heq
    exact heq
  have htarget : T.target ⊆ (data.modelDisk i).source := by
    intro y hy
    simpa only [T.right_inv hy] using (hT _ (T.map_target hy)).2.1
  have ha : ContDiffOn Real ∞ a T.target := by
    intro y hy
    have hF := (contDiffOn_actualCapModelCoordinates data hg H i).contDiffAt
      ((data.actualDisk i).open_source.mem_nhds (hTs (T.map_target hy)))
    have hTinv := T.contMDiffOn_invFun.contMDiffAt (T.open_target.mem_nhds hy)
    exact (((contDiffAt_norm Real (hnonzero y hy)).comp y
      (hF.comp y hTinv.contDiffAt)).sub contDiffAt_const).contDiffWithinAt
  have hzero (y : E2) (hy : F (T.symm y) ∈ sphere (0 : E3) 1) : a y = 0 := by
    change ‖F (T.symm y)‖ - 1 = 0
    rw [mem_sphere_zero_iff_norm] at hy
    exact sub_eq_zero.mpr hy
  have haCircle : EqOn a (fun _ => 0) (sphere (0 : E2) 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hTi.symm ▸ hy
    change ‖F (T.symm (T x))‖ - 1 = 0
    have hinv : T.symm (T x) = x := T.left_inv (hTc hx)
    rw [hinv]
    obtain ⟨r, hr, _, houter, _⟩ :=
      exists_actual_terminal_sphere_projection data hg Φ χ H hH hχ hplanar i
    have hxouter : x ∈ closedBall (0 : E2) r \ ball 0 1 :=
      ⟨closedBall_subset_closedBall hr.le (sphere_subset_closedBall hx),
        fun hb => (ne_of_lt (mem_ball.mp hb)) (mem_sphere.mp hx)⟩
    exact sub_eq_zero.mpr (mem_sphere_zero_iff_norm.mp (houter hxouter))
  refine ⟨T, a, hTc, hTi, hTs, htarget, ha, haCircle, ?_,
    (fun y _ hy => hzero y hy), ?_⟩
  · intro y hy
    refine ⟨by dsimp [a]; linarith [norm_pos_iff.mpr (hnonzero y hy)], ?_⟩
    have heq := congrArg (fun q : S2 => (q : E3)) (hproj y hy)
    rw [sphereProjection_coe (hnonzero y hy)] at heq
    rw [heq]
    dsimp [a]
    rw [show 1 + (‖F (T.symm y)‖ - 1) = ‖F (T.symm y)‖ by ring,
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hnonzero y hy)), one_smul]
  · let s : S2 → E3 := H ∘ data.toTerminalSaddleGeometry.flatten ∘ g
    let n : E2 → E3 := fun y => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y))
    have hs : Topology.IsEmbedding s := H.toHomeomorph.isEmbedding.comp
      (data.toTerminalSaddleGeometry.flatten.toHomeomorph.isEmbedding.comp
        (M.tree.embedding_of_mem_leaves hg).isEmbedding)
    obtain ⟨U, hU, hchartU, hcover⟩ := exists_surface_neighborhood_in_chart
      hs (data.actualDisk i) T.open_source hTs
    have hband := terminal_band_image data Φ χ H hH hχ hplanar
    have hbandrange : data.toTerminalSaddleGeometry.modelBand ⊆ range s := by
      rw [show range s = H '' (data.toTerminalSaddleGeometry.flatten '' range g) by
        simp only [s, range_comp], ← hband]
      apply image_mono
      rw [data.actual_decomposition]
      exact subset_union_left
    have hn : ContinuousOn n T.target :=
      (data.toTerminalSaddleGeometry.flatten.contMDiff.comp_contMDiffOn
        (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp_contMDiffOn
          (contMDiff_coe_sphere.comp_contMDiffOn
            (data.modelDisk_smooth i)))).continuousOn.mono htarget
    let V := T.target ∩ n ⁻¹' U
    have hV : IsOpen V := hn.isOpen_inter_preimage T.open_target hU
    have hcircleV : sphere (0 : E2) 1 ⊆ V := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hTi.symm ▸ hy
      have hxt := hTc hx
      have hyt : y ∈ T.target := hxy ▸ T.map_source hxt
      refine ⟨hyt, ?_⟩
      have hFx : F x = (data.modelDisk i y : E3) := by
        have hz : ‖F x‖ = 1 := by
          have haz := haCircle hy
          have hinv : T.symm y = x := hxy ▸ T.left_inv hxt
          change ‖F (T.symm y)‖ - 1 = 0 at haz
          rw [hinv] at haz
          linarith
        have hp := congrArg (fun q : S2 => (q : E3)) (hT x hxt).2.2
        rw [hxy, sphereProjection_coe (hT x hxt).1, hz, inv_one, one_smul] at hp
        exact hp.symm
      have heq : n y = s (data.actualDisk i x) := by
        have hh := congrArg (fun z => data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel z)) hFx
        simp only [F, actualCapModelCoordinates, Diffeomorph.apply_symm_apply] at hh
        exact hh.symm
      change n y ∈ U
      rw [heq]
      exact hchartU (mem_image_of_mem (s ∘ data.actualDisk i) hxt)
    refine ⟨V, hV, hcircleV, inter_subset_left, ?_⟩
    intro y hy hyband
    obtain ⟨x, hx, hxy⟩ := hcover ⟨hbandrange hyband, hy.2⟩
    have hFx : F x = (data.modelDisk i y : E3) := by
      have hh := congrArg (fun z => data.toTerminalSaddleGeometry.filledModel.symm
        (data.toTerminalSaddleGeometry.flatten.symm z)) hxy
      simp only [Diffeomorph.symm_apply_apply] at hh
      exact hh
    have hTx : T x = y := by
      apply (data.modelDisk i).injOn (hT x hx).2.1 (htarget hy.1)
      rw [(hT x hx).2.2]
      change sphereProjection (F x) = _
      rw [hFx, sphereProjection_sphere]
    have hinv : T.symm y = x := hTx ▸ T.left_inv hx
    apply hzero
    rw [hinv, hFx]
    exact (data.modelDisk i y).property

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
