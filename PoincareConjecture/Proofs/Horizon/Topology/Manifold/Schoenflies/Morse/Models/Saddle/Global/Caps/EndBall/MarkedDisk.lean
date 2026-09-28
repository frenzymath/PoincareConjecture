import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.DiskBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.ClosingDisk
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Immersion.FiniteDimensional



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_ball_with_closing_disk_of_sphere_disk_with_boundary_intersection
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (m : OpenPartialHomeomorph E2 S2) (hms : closedBall 0 1 ⊆ m.source)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    {W : Set E3} (hW : IsOpen W) (hDW : g '' (m '' closedBall 0 1) ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (d : E2 → E3) (U : Set E3),
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧
      IsOpen U ∧ g '' (m '' closedBall 0 1) ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      range d ⊆ B '' sphere (0 : E3) 1 ∧
      g '' (m '' closedBall 0 1) = (B '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (B '' sphere (0 : E3) 1) ∩ U = range g ∩ U ∧
      (B '' closedBall (0 : E3) 1) ∩ range g ⊆ B '' sphere (0 : E3) 1 ∧
      g '' (m '' ball 0 1) =
        (B '' sphere (0 : E3) 1) \ d '' closedBall (0 : E2) 1 := by
  let mp : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { m with contMDiffOn_toFun := hm, contMDiffOn_invFun := hmi }
  obtain ⟨B, U, hU, hDU, hBW, hBU, hBm, hBinter⟩ :=
    exists_ball_along_sphere_disk_with_boundary_intersection hg m
    (m.injOn.mono hms) (fun x hx => mp.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hms hx))
    hW (by simpa only [image_comp] using hDW)
  obtain ⟨n, hns, hn, hni, hnc, hno⟩ := exists_global_complementary_disk_chart m
    (m.injOn.mono hms) (fun x hx => mp.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ (hms hx))
  let np : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
    { n with contMDiffOn_toFun := hn.contMDiffOn, contMDiffOn_invFun := hni }
  let b : S2 → E3 := fun p => B p
  let d : E2 → E3 := b ∘ n
  have hb : ContMDiff (𝓡 2) (𝓡 3) ∞ b := B.contMDiff.comp contMDiff_coe_sphere
  have hbi : Injective b := B.injective.comp Subtype.val_injective
  have hbder (p : S2) : Injective (mfderiv (𝓡 2) (𝓡 3) b p) := by
    change Injective (mfderiv (𝓡 2) (𝓡 3) (B ∘ (Subtype.val : S2 → E3)) p)
    rw [mfderiv_comp p (B.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp) p)]
    exact (B.mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere p)
  have hdder (x : E2) : Injective (fderiv Real d x) := by
    suffices hh : Injective (mfderiv (𝓡 2) (𝓡 3) (b ∘ n) x) by
      simpa only [mfderiv_eq_fderiv, TangentSpace, d] using hh
    rw [mfderiv_comp x (hb.mdifferentiable (by simp) _) (hn.mdifferentiable (by simp) _)]
    exact (hbder (n x)).comp ((np.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞
      (hns ▸ mem_univ x)).mfderivToContinuousLinearEquiv (by simp)).injective
  have hde : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d := by
    refine ⟨Poincare.Geometry.Manifold.isImmersion_of_injective_mfderiv (hb.comp hn) ?_, ?_⟩
    · intro x
      simpa only [mfderiv_eq_fderiv, TangentSpace] using hdder x
    · exact B.toHomeomorph.isEmbedding.comp
        (Topology.IsEmbedding.subtypeVal.comp (n.isOpenEmbedding hns).isEmbedding)
  have hbm : b '' (m '' closedBall 0 1) = g '' (m '' closedBall 0 1) := by
    rw [image_image, image_image]
    exact image_congr hBm
  have hbuniv : b '' univ = B '' sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨p, _, rfl⟩
      exact mem_image_of_mem B p.property
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, mem_univ _, rfl⟩
  refine ⟨B, d, U, hde, hdder, hU,
    (by simpa only [image_comp] using hDU), hBW, ?_, ?_, hBU, hBinter, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact mem_image_of_mem B (n x).property
  · rw [← hbm]
    calc
      b '' (m '' closedBall 0 1) = b '' (univ \ (n '' ball (0 : E2) 1)) := by
        rw [hno]
        congr 1
        ext p
        simp
      _ = (b '' univ) \ (b '' (n '' ball (0 : E2) 1)) := image_sdiff hbi _ _
      _ = _ := by rw [hbuniv, image_image]; rfl
  · have hbmo : b '' (m '' ball 0 1) = g '' (m '' ball 0 1) := by
      rw [image_image, image_image]
      exact image_congr (fun x hx => hBm x (ball_subset_closedBall hx))
    rw [← hbmo]
    calc
      b '' (m '' ball 0 1) = b '' (univ \ (n '' closedBall (0 : E2) 1)) := by
        rw [hnc]
        congr 1
        ext p
        simp
      _ = (b '' univ) \ (b '' (n '' closedBall (0 : E2) 1)) := image_sdiff hbi _ _
      _ = _ := by rw [hbuniv, image_image]; rfl

theorem exists_ball_with_closing_disk_of_sphere_disk
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (m : OpenPartialHomeomorph E2 S2) (hms : closedBall 0 1 ⊆ m.source)
    (hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    {W : Set E3} (hW : IsOpen W) (hDW : g '' (m '' closedBall 0 1) ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (d : E2 → E3) (U : Set E3),
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ d ∧
      (∀ x, Injective (fderiv Real d x)) ∧
      IsOpen U ∧ g '' (m '' closedBall 0 1) ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      range d ⊆ B '' sphere (0 : E3) 1 ∧
      g '' (m '' closedBall 0 1) = (B '' sphere (0 : E3) 1) \ d '' ball (0 : E2) 1 ∧
      (B '' sphere (0 : E3) 1) ∩ U = range g ∩ U := by
  obtain ⟨B, d, U, hd, hdi, hU, hDU, hBW, hdB, hcomp, hBU, _⟩ :=
    exists_ball_with_closing_disk_of_sphere_disk_with_boundary_intersection
      hg m hms hm hmi hW hDW
  exact ⟨B, d, U, hd, hdi, hU, hDU, hBW, hdB, hcomp, hBU⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps
