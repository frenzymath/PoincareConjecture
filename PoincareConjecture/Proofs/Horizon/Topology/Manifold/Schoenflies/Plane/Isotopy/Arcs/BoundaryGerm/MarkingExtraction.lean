import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric IsManifold
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm

private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩



theorem exists_boundary_marking_in_open
    (q : S1) (U : Set S1) (hU : IsOpen U) (hq : q ∈ U) :
    ∃ f : E1 → S1, f 0 = q ∧ InjOn f (closedBall 0 2) ∧
      (∀ x, x ∈ closedBall (0 : E1) 2 →
        IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) ∧
      f '' closedBall 0 2 ⊆ U := by
  let s := stereographic' 1 (-q)
  have hs : s ∈ maximalAtlas (𝓡 1) ∞ S1 :=
    IsManifold.subset_maximalAtlas ⟨-q, rfl⟩
  have hqt : q ∈ s.source := by
    simpa only [s, stereographic'_source, mem_compl_iff, mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere Real q
  have hsi : ContMDiff (𝓡 1) (𝓡 1) ∞ s.symm := by
    rw [← contMDiffOn_univ]
    simpa only [s, stereographic'_target] using contMDiffOn_symm_of_mem_maximalAtlas hs
  have hpre : IsOpen (s.symm ⁻¹' U) := hU.preimage hsi.continuous
  have hp : s q ∈ s.symm ⁻¹' U := by simpa only [mem_preimage, s.left_inv hqt] using hq
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hpre (s q) hp
  let a : Real := δ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let L : Diffeomorph (𝓡 1) (𝓡 1) E1 E1 ∞ :=
    { toFun := fun x => s q + a • x
      invFun := fun y => a⁻¹ • (y - s q)
      left_inv := by intro x; simp [smul_smul, ne_of_gt ha]
      right_inv := by intro y; simp [smul_smul, ne_of_gt ha]
      contMDiff_toFun := (show ContDiff Real ∞ (fun x : E1 => s q + a • x) from
        contDiff_const.add (contDiff_id.const_smul a)).contMDiff
      contMDiff_invFun := (show ContDiff Real ∞ (fun y : E1 => a⁻¹ • (y - s q)) from
        (contDiff_id.sub contDiff_const).const_smul a⁻¹).contMDiff }
  let d : PartialDiffeomorph (𝓡 1) (𝓡 1) E1 S1 ∞ :=
    { toPartialEquiv := s.symm.toPartialEquiv
      open_source := s.open_target
      open_target := s.open_source
      contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hs
      contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hs }
  have hds (x : E1) : x ∈ d.source := by
    change x ∈ s.target
    simp only [s, stereographic'_target, mem_univ]
  refine ⟨s.symm ∘ L, ?_, ?_, ?_, ?_⟩
  · change s.symm (s q + a • (0 : E1)) = q
    rw [smul_zero, add_zero]
    exact s.left_inv hqt
  · intro x hx y hy hxy
    apply L.injective
    exact s.symm.injOn (hds _) (hds _) hxy
  · intro x hx
    exact (L.isLocalDiffeomorph x).comp (𝓡 1) S1
      (d.isLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ (hds (L x)))
  · rintro _ ⟨x, hx, rfl⟩
    apply hball
    change dist (s q + a • x) (s q) < δ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hx' : ‖x‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hx
    have hbound := mul_le_mul_of_nonneg_left hx' ha.le
    dsimp [a] at hbound ⊢
    linarith




theorem exists_common_boundary_marking_of_eqOn
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (q : S1) (W : Set E2) (hW : IsOpen W) (hqW : (q : E2) ∈ W)
    (hAB : EqOn A B W)
    (V : Set E2) (hV : IsOpen V) (hqV : A q ∈ V) :
    ∃ f : E1 → S1, f 0 = q ∧ InjOn f (closedBall 0 2) ∧
      (∀ x, x ∈ closedBall (0 : E1) 2 →
        IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x) ∧
      (∀ x, x ∈ closedBall (0 : E1) 2 → A (f x) = B (f x)) ∧
      (fun x => A (f x)) '' closedBall 0 2 ⊆ V := by
  let U : Set S1 := Subtype.val ⁻¹' W ∩ (fun z : S1 => A z) ⁻¹' V
  have hU : IsOpen U := (hW.preimage continuous_subtype_val).inter
    (hV.preimage (A.continuous.comp continuous_subtype_val))
  obtain ⟨f, hf0, hfi, hfl, hfU⟩ := exists_boundary_marking_in_open q U hU ⟨hqW, hqV⟩
  refine ⟨f, hf0, hfi, hfl, ?_, ?_⟩
  · intro x hx
    exact hAB (hfU (mem_image_of_mem f hx)).1
  · rintro _ ⟨x, hx, rfl⟩
    exact (hfU (mem_image_of_mem f hx)).2

end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
