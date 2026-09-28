import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.TerminalCollars
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SphereProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.ProjectionChart



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


def actualCapModelCoordinates (data : TerminalSaddleData M P p e)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3) (x : E2) : E3 :=
  data.toTerminalSaddleGeometry.filledModel.symm
    (data.toTerminalSaddleGeometry.flatten.symm
      (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i x)))))

theorem contDiffOn_actualCapModelCoordinates
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3) :
    ContDiffOn Real ∞ (actualCapModelCoordinates data H i) (data.actualDisk i).source := by
  let A := data.toTerminalSaddleGeometry.flatten.trans
    (H.trans (data.toTerminalSaddleGeometry.flatten.symm.trans
      data.toTerminalSaddleGeometry.filledModel.symm))
  exact (A.contMDiff.comp_contMDiffOn
    ((M.tree.embedding_of_mem_leaves hg).contMDiff.comp_contMDiffOn
      (data.actualDisk_smooth i))).contDiffOn

theorem injective_fderiv_actualCapModelCoordinates
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3)
    {x : E2} (hx : x ∈ (data.actualDisk i).source) :
    Injective (fderiv Real (actualCapModelCoordinates data H i) x) := by
  let A := data.toTerminalSaddleGeometry.flatten.trans
    (H.trans (data.toTerminalSaddleGeometry.flatten.symm.trans
      data.toTerminalSaddleGeometry.filledModel.symm))
  let m : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { data.actualDisk i with
      contMDiffOn_toFun := data.actualDisk_smooth i
      contMDiffOn_invFun := data.actualDisk_symm_smooth i }
  have hm := m.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ hx
  have hs := M.tree.embedding_of_mem_leaves hg
  rw [← mfderiv_eq_fderiv]
  change Injective (mfderiv (𝓡 2) (𝓡 3) (A ∘ g ∘ (m : E2 → S2)) x)
  rw [mfderiv_comp x (A.contMDiff.mdifferentiable (by simp) _)
    ((hs.contMDiff.contMDiffAt.comp x hm.contMDiffAt).mdifferentiableAt (by simp))]
  apply (A.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
  rw [mfderiv_comp x (hs.contMDiff.mdifferentiable (by simp) _) (hm.mdifferentiableAt (by simp))]
  exact (injective_mfderiv_sphere_embedding hs _).comp
    (hm.mfderivToContinuousLinearEquiv (by simp)).injective



theorem exists_actual_terminal_sphere_projection
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (i : Fin 3) :
    ∃ r : Real, 1 < r ∧ closedBall 0 r ⊆ (data.actualDisk i).source ∧
      MapsTo (actualCapModelCoordinates data H i)
        (closedBall (0 : E2) r \ ball 0 1) (sphere (0 : E3) 1) ∧
      ∀ q ∈ sphere (0 : E2) 1,
        Injective (mfderiv (𝓡 2) (𝓡 2)
          (sphereProjection ∘ actualCapModelCoordinates data H i) q) := by
  obtain ⟨r, hr, hsource, houter⟩ := exists_actual_terminal_outer_annulus data hg i
  have hband := terminal_band_image data Φ χ H hH hχ hplanar
  have hsubset : data.toTerminalSaddleGeometry.modelBand ⊆
      data.toTerminalSaddleGeometry.flatten ''
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
    rw [data.model_decomposition]
    exact subset_union_left
  have hsphere : MapsTo (actualCapModelCoordinates data H i)
      (closedBall (0 : E2) r \ ball 0 1) (sphere (0 : E3) 1) := by
    intro x hx
    have hmem := hsubset (hband ▸ mem_image_of_mem H (houter (mem_image_of_mem _ hx)))
    obtain ⟨y, ⟨z, hz, rfl⟩, heq⟩ := hmem
    simp only [comp_apply] at heq
    change data.toTerminalSaddleGeometry.filledModel.symm
      (data.toTerminalSaddleGeometry.flatten.symm
        (H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i x))))) ∈ _
    rw [← heq, Diffeomorph.symm_apply_apply, Diffeomorph.symm_apply_apply]
    exact hz
  refine ⟨r, hr, hsource, hsphere, ?_⟩
  intro q hq
  have hqs := data.actualDisk_source i (sphere_subset_closedBall hq)
  exact injective_mfderiv_sphereProjection_comp hr hsphere hq
    ((contDiffOn_actualCapModelCoordinates data hg H i).contDiffAt
      ((data.actualDisk i).open_source.mem_nhds hqs))
    (injective_fderiv_actualCapModelCoordinates data hg H i hqs)



theorem exists_actual_terminal_projection_chart
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
    ∃ T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      ∀ x ∈ T.source, actualCapModelCoordinates data H i x ≠ 0 ∧
        T x ∈ (data.modelDisk i).source ∧
        data.modelDisk i (T x) = sphereProjection (actualCapModelCoordinates data H i x) := by
  let F := actualCapModelCoordinates data H i
  let m := data.modelDisk i
  let k : E2 → E2 := m.symm ∘ sphereProjection ∘ F
  obtain ⟨r, hr, _, houter, _⟩ :=
    exists_actual_terminal_sphere_projection data hg Φ χ H hH hχ hplanar i
  obtain ⟨R, hRc, hRb, hR⟩ :=
    exists_terminal_boundary_reparametrization data hg Φ χ H hH hχ hplanar hlabels i
  have hRcircle : R '' sphere (0 : E2) 1 = sphere (0 : E2) 1 := by
    rw [← closedBall_sdiff_ball, image_sdiff (f := (R : E2 → E2)) R.injective, hRc, hRb]
  have hRsource (x : E2) (hx : x ∈ sphere (0 : E2) 1) : R x ∈ m.source :=
    data.modelDisk_source i (sphere_subset_closedBall (hRcircle ▸ mem_image_of_mem R hx))
  have hFcircle (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      F x = (m (R x) : E3) := by
    have heq := congrArg (fun y => data.toTerminalSaddleGeometry.filledModel.symm
      (data.toTerminalSaddleGeometry.flatten.symm y)) (hR x hx)
    simp only [Diffeomorph.symm_apply_apply] at heq
    exact heq.symm
  have hPcircle (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      sphereProjection (F x) = m (R x) := by rw [hFcircle x hx, sphereProjection_sphere]
  have hkcircle : EqOn k R (sphere (0 : E2) 1) := by
    intro x hx
    change m.symm (sphereProjection (F x)) = R x
    rw [hPcircle x hx, m.left_inv (hRsource x hx)]
  have htarget (x : E2) (hx : x ∈ sphere (0 : E2) 1) : sphereProjection (F x) ∈ m.target := by
    rw [hPcircle x hx]
    exact m.map_source (hRsource x hx)
  have hF := contDiffOn_actualCapModelCoordinates data hg H i
  have hlocal := localDiffeomorphAt_projection_chart_on_rim
    (data.actualDisk i).open_source
    (sphere_subset_closedBall.trans (data.actualDisk_source i)) hF hr houter
    (fun x hx => injective_fderiv_actualCapModelCoordinates data hg H i
      (data.actualDisk_source i (sphere_subset_closedBall hx)))
    m (data.modelDisk_smooth i) (data.modelDisk_symm_smooth i) htarget
  obtain ⟨n, hn, _, hnk, hns, hnsi⟩ := Poincare.exists_openPartialHomeomorph_of_injOn_compact
    (isCompact_sphere (0 : E2) 1)
    (show InjOn k (sphere (0 : E2) 1) from fun x hx y hy hxy =>
      R.injective ((hkcircle hx).symm.trans (hxy.trans (hkcircle hy)))) hlocal
  let V := (data.actualDisk i).source ∩ F ⁻¹' ({0}ᶜ : Set E3)
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage
    (data.actualDisk i).open_source isClosed_singleton.isOpen_compl
  have hP : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (sphereProjection ∘ F) V := by
    intro x hx
    exact ((contMDiffAt_sphereProjection hx.2).comp x
      ((hF x hx.1).contDiffAt ((data.actualDisk i).open_source.mem_nhds hx.1)).contMDiffAt).contMDiffWithinAt
  let U := V ∩ (sphereProjection ∘ F) ⁻¹' m.target
  have hU : IsOpen U := hP.continuousOn.isOpen_inter_preimage hV m.open_target
  have hcircleU : sphere (0 : E2) 1 ⊆ U := by
    intro x hx
    refine ⟨⟨data.actualDisk_source i (sphere_subset_closedBall hx), ?_⟩, htarget x hx⟩
    change F x ≠ 0
    rw [hFcircle x hx]
    exact ne_zero_of_mem_unit_sphere (m (R x))
  let T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    { n.restr U with
      contMDiffOn_toFun := hns.mono (fun _ hx => hx.1)
      contMDiffOn_invFun := hnsi.mono (fun _ hx => hx.1) }
  have hTsource : T.source = n.source ∩ U := by
    change n.source ∩ interior U = n.source ∩ U
    rw [hU.interior_eq]
  have hTc : sphere (0 : E2) 1 ⊆ T.source := by rw [hTsource]; exact subset_inter hn hcircleU
  have hTapply (x : E2) : T x = n x := rfl
  refine ⟨T, hTc, ?_, ?_, ?_⟩
  · calc
      T '' sphere (0 : E2) 1 = R '' sphere (0 : E2) 1 := image_congr (fun x hx =>
        (hnk (hn hx)).trans (hkcircle hx))
      _ = _ := hRcircle
  · rw [hTsource]
    exact fun x hx => hx.2.1.1
  · intro x hx
    rw [hTsource] at hx
    have heq : T x = m.symm (sphereProjection (F x)) := (hTapply x).trans (hnk hx.1)
    refine ⟨hx.2.1.2, ?_, ?_⟩
    · rw [heq]
      exact m.map_target hx.2.2
    · rw [heq]
      exact m.right_inv hx.2.2

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
