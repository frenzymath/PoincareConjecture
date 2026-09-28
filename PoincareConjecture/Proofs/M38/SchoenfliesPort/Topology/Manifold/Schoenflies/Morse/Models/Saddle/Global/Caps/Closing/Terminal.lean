import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.MarkedDisk
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Reparametrize
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.TerminalObstacles

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
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
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

open SaddleLevel

private theorem postcompose_sphere_embedding
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F ∘ g) := by
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (F.contMDiff.comp hg.contMDiff) (F.injective.comp hg.isEmbedding.injective)
  intro q
  rw [mfderiv_comp q (F.contMDiff.mdifferentiable (by simp) _)
    (hg.contMDiff.mdifferentiable (by simp) q)]
  exact (F.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
    (injective_mfderiv_sphere_embedding hg q)

private theorem ambient_sphere_embedding
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q : S2 => F q) := by
  have hc := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (F.contMDiff.comp hc) (F.injective.comp Subtype.val_injective)
  intro q
  rw [mfderiv_comp q (F.contMDiff.mdifferentiable (by simp) _)
    (hc.mdifferentiable (by simp) q)]
  apply (F.mfderivToContinuousLinearEquiv (by simp) (q : E3)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere q

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_actual_terminal_cap_complement
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (i : Fin 3)
    {W : Set E3} (hW : IsOpen W)
    (hCW : H '' data.toTerminalSaddleGeometry.C i ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (d : E2 → E3) (U : Set E3),
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧
      IsOpen U ∧ H '' data.toTerminalSaddleGeometry.C i ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      range d ⊆ B '' sphere (0 : E3) 1 ∧
      H '' data.toTerminalSaddleGeometry.C i =
        (B '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (B '' sphere (0 : E3) 1) ∩ U =
        (H '' (data.toTerminalSaddleGeometry.flatten '' range g)) ∩ U ∧
      (B '' closedBall (0 : E3) 1) ∩
        (H '' (data.toTerminalSaddleGeometry.flatten '' range g)) ⊆ B '' sphere (0 : E3) 1 ∧
      H '' ((data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
        ball (0 : E2) 1) = (B '' sphere (0 : E3) 1) \ d '' closedBall (0 : E2) 1 ∧
      (B '' closedBall (0 : E3) 1) ∩ (H '' data.toTerminalSaddleGeometry.actualBand) ⊆
        d '' closedBall (0 : E2) 1 := by
  let F := data.toTerminalSaddleGeometry.flatten.trans H
  have hF := postcompose_sphere_embedding (M.tree.embedding_of_mem_leaves hg) F
  have hcap : (F ∘ g) '' (data.actualDisk i '' closedBall 0 1) =
      H '' data.toTerminalSaddleGeometry.C i := by
    rw [data.actualDisk_image]
    simp only [TerminalSaddleGeometry.C, image_image, comp_def, F]
    rfl
  have hrange : range (F ∘ g) =
      H '' (data.toTerminalSaddleGeometry.flatten '' range g) := by
    simp only [← range_comp, comp_def, F]
    rfl
  obtain ⟨B, d, U, hd, hdi, hU, hCU, hBW, hdB, hcomp, hBU, hBi, hBo⟩ :=
    exists_ball_with_closing_disk_of_sphere_disk_with_boundary_intersection hF (data.actualDisk i)
      (data.actualDisk_source i) (data.actualDisk_smooth i)
      (data.actualDisk_symm_smooth i) hW (hcap ▸ hCW)
  have hopen : H '' ((data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
      ball (0 : E2) 1) = (B '' sphere (0 : E3) 1) \ d '' closedBall (0 : E2) 1 := by
    simp only [image_image] at hBo ⊢
    exact hBo
  have hBi' := hrange ▸ hBi
  refine ⟨B, d, U, hd, hdi, hU, hcap ▸ hCU, hBW, hdB, hcap ▸ hcomp,
    hrange ▸ hBU, hBi', hopen, ?_⟩
  rintro y ⟨hyB, hyband⟩
  by_contra hy
  have hsub : data.toTerminalSaddleGeometry.actualBand ⊆
      data.toTerminalSaddleGeometry.flatten '' range g := by
    rw [data.actual_decomposition]
    exact subset_union_left
  have hyS := hBi' ⟨hyB, image_mono hsub hyband⟩
  have hdis := disjoint_image_of_injective (f := (H : E3 → E3)) H.injective
    (actual_terminal_cap_interior_disjoint_band data hg i)
  exact disjoint_left.mp hdis (hopen.symm ▸ ⟨hyS, hy⟩) hyband

theorem exists_model_terminal_cap_complement
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    {W : Set E3} (hW : IsOpen W)
    (hCW : data.toTerminalSaddleGeometry.modelCaps i ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (d : E2 → E3) (U : Set E3),
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧
      IsOpen U ∧ data.toTerminalSaddleGeometry.modelCaps i ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      range d ⊆ B '' sphere (0 : E3) 1 ∧
      data.toTerminalSaddleGeometry.modelCaps i =
        (B '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (B '' sphere (0 : E3) 1) ∩ U =
        (data.toTerminalSaddleGeometry.flatten ''
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ∩ U ∧
      (B '' closedBall (0 : E3) 1) ∩ (data.toTerminalSaddleGeometry.flatten ''
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)) ⊆
          B '' sphere (0 : E3) 1 ∧
      (fun x => data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) '' ball (0 : E2) 1 =
          (B '' sphere (0 : E3) 1) \ d '' closedBall (0 : E2) 1 ∧
      (B '' closedBall (0 : E3) 1) ∩ data.toTerminalSaddleGeometry.modelBand ⊆
        d '' closedBall (0 : E2) 1 := by
  let F := data.toTerminalSaddleGeometry.filledModel.trans
    data.toTerminalSaddleGeometry.flatten
  let s : S2 → E3 := fun q => F q
  have hcap : s '' (data.modelDisk i '' closedBall 0 1) =
      data.toTerminalSaddleGeometry.modelCaps i := by
    rw [data.modelDisk_image]
    rfl
  have hrange : range s = data.toTerminalSaddleGeometry.flatten ''
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem _ q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  obtain ⟨B, d, U, hd, hdi, hU, hCU, hBW, hdB, hcomp, hBU, hBi, hBo⟩ :=
    exists_ball_with_closing_disk_of_sphere_disk_with_boundary_intersection
      (ambient_sphere_embedding F)
      (data.modelDisk i) (data.modelDisk_source i) (data.modelDisk_smooth i)
      (data.modelDisk_symm_smooth i) hW (hcap ▸ hCW)
  have hopen : (fun x => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) '' ball (0 : E2) 1 =
        (B '' sphere (0 : E3) 1) \ d '' closedBall (0 : E2) 1 := by
    rw [image_image] at hBo
    exact hBo
  have hBi' := hrange ▸ hBi
  refine ⟨B, d, U, hd, hdi, hU, hcap ▸ hCU, hBW, hdB, hcap ▸ hcomp,
    hrange ▸ hBU, hBi', hopen, ?_⟩
  rintro y ⟨hyB, hyband⟩
  by_contra hy
  have hsub : data.toTerminalSaddleGeometry.modelBand ⊆
      data.toTerminalSaddleGeometry.flatten ''
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
    rw [data.model_decomposition]
    exact subset_union_left
  have hyS := hBi' ⟨hyB, hsub hyband⟩
  exact disjoint_left.mp (model_terminal_cap_interior_disjoint_band data i)
    (hopen.symm ▸ ⟨hyS, hy⟩) hyband

private theorem lift_image_slice
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (S : Set E2) (z : Real) :
    H '' Saddle.slice S z = Saddle.slice (Φ (χ z) z '' S) z := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  have hproj (x : E2) (c : Real) : Saddle.toE2 (Saddle.toE3 x c) = x := by
    ext i
    fin_cases i <;> rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Saddle.toE2 x ∈ S ∧ x 2 = z at hx
    rw [hH]
    change Saddle.toE2 (Saddle.toE3 _ (x 2)) ∈ Φ (χ z) z '' S ∧ x 2 = z
    rw [hproj, hx.2]
    exact ⟨mem_image_of_mem _ hx.1, rfl⟩
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    refine ⟨Saddle.toE3 x z, ⟨?_, rfl⟩, ?_⟩
    · simpa only [hproj] using hx
    · rw [hH]
      change Saddle.toE3 (Φ (χ z) z (Saddle.toE2 (Saddle.toE3 x z))) z = y
      rw [hproj, hxy, ← hy, hcoord]

theorem terminal_band_image
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z) :
    H '' data.toTerminalSaddleGeometry.actualBand = data.toTerminalSaddleGeometry.modelBand := by
  exact Saddle.image_iUnion_slice_parametric_of_matching Φ χ _ _ H
    (lift_image_slice Φ χ H hH) hχ hplanar

theorem terminal_cap_band_inter_image
    (data : TerminalSaddleData M P p e)
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
    (H '' data.toTerminalSaddleGeometry.C i) ∩ data.toTerminalSaddleGeometry.modelBand =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
  conv_lhs =>
    rw [← terminal_band_image data Φ χ H hH hχ hplanar,
      ← image_inter (f := (H : E3 → E3)) H.injective]
  rw [← hlabels i]
  apply image_congr
  intro y hy
  obtain ⟨z, hyz⟩ := mem_iUnion.mp hy.2
  obtain ⟨hz, hyz⟩ := mem_iUnion.mp hyz
  rw [hH, hχ (y 2) (hyz.2 ▸ hz)]

private theorem disk_boundary_embedding
    {s : S2 → E3} (hs : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ s)
    (m : OpenPartialHomeomorph E2 S2) (hms : closedBall 0 1 ⊆ m.source)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞
      (fun q : S1 => s (m q)) := by
  let mp : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { m with contMDiffOn_toFun := hm, contMDiffOn_invFun := hmi }
  have hsrc (q : S1) : (q : E2) ∈ m.source := hms (sphere_subset_closedBall q.property)
  have hmc : ContMDiff (𝓡 1) (𝓡 2) ∞ (fun q : S1 => m q) :=
    hm.comp_contMDiff contMDiff_coe_sphere hsrc
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (hs.contMDiff.comp hmc)
    (fun q r h => Subtype.val_injective (m.injOn (hsrc q) (hsrc r)
      (hs.isEmbedding.injective h)))
  intro q
  rw [mfderiv_comp q (hs.contMDiff.mdifferentiable (by simp) _)
    (hmc.mdifferentiable (by simp) q)]
  apply (injective_mfderiv_sphere_embedding hs (m q)).comp
  change Injective (mfderiv (𝓡 1) (𝓡 2)
    ((m : E2 → S2) ∘ (Subtype.val : S1 → E2)) q)
  rw [mfderiv_comp q
    (((hm q (hsrc q)).contMDiffAt (m.open_source.mem_nhds (hsrc q))).mdifferentiableAt (by simp))
    ((contMDiff_coe_sphere (n := 1) (m := ∞) (E := E2)).mdifferentiable (by simp) q)]
  apply ((mp.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hsrc q)).mfderivToContinuousLinearEquiv
    (by simp)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere q

theorem exists_terminal_boundary_reparametrization
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
    ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      R '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      R '' ball (0 : E2) 1 = ball (0 : E2) 1 ∧
      ∀ x ∈ sphere (0 : E2) 1,
        data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i (R x))) =
            H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i x))) := by
  let a : S1 → E3 := fun q => H (data.toTerminalSaddleGeometry.flatten (g (data.actualDisk i q)))
  let b : S1 → E3 := fun q => data.toTerminalSaddleGeometry.flatten
    (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q))
  have ha := disk_boundary_embedding
    (postcompose_sphere_embedding (M.tree.embedding_of_mem_leaves hg)
      (data.toTerminalSaddleGeometry.flatten.trans H))
    (data.actualDisk i) (data.actualDisk_source i) (data.actualDisk_smooth i)
    (data.actualDisk_symm_smooth i)
  have hb := disk_boundary_embedding
    (ambient_sphere_embedding (data.toTerminalSaddleGeometry.filledModel.trans
      data.toTerminalSaddleGeometry.flatten))
    (data.modelDisk i) (data.modelDisk_source i) (data.modelDisk_smooth i)
    (data.modelDisk_symm_smooth i)
  have hrange : range a = range b := by
    have h := terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i
    conv_lhs at h =>
      rw [← terminal_band_image data Φ χ H hH hχ hplanar,
        ← image_inter (f := (H : E3 → E3)) H.injective, data.actual_boundary]
    rw [data.model_boundary, image_image] at h
    simpa only [image_eq_range, comp_def] using h
  obtain ⟨q, hq⟩ := ha.exists_reparametrizing_diffeomorph hb hrange
  obtain ⟨R, hR, hRc, hRo⟩ := exists_ambient_diffeomorph_of_circle_diffeomorph q
  refine ⟨R, hRc, hRo, ?_⟩
  intro x hx
  rw [hR ⟨x, hx⟩]
  exact hq ⟨x, hx⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
