import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.StereographicReduction
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialExtension










set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in


@[simp] theorem spherePlaneChart_neg_apply (p : UnitTwoSphere) :
    spherePlaneChart (-p) p = 0 := by
  have hs : stereographic' 2 (-p) p = 0 := by
    dsimp [stereographic']
    simp only [EmbeddingLike.map_eq_zero_iff]
    exact stereographic_neg_apply p
  simp [spherePlaneChart, hs]



@[simp] theorem spherePlaneChart_neg_symm_zero (p : UnitTwoSphere) :
    (spherePlaneChart (-p)).symm 0 = p := by
  rw [← spherePlaneChart_neg_apply p]
  apply (spherePlaneChart (-p)).left_inv
  simpa only [spherePlaneChart_source, mem_compl_iff, mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ p




theorem exists_local_sphere_identity_germ (p : UnitTwoSphere)
    (g : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) (Q : E3 → E3)
    (hQ : DifferentiableAt ℝ Q (p : E3)) (hQp : Q (p : E3) = (p : E3))
    (hDQ : fderiv ℝ Q (p : E3) = ContinuousLinearMap.id ℝ E3)
    (hgQ : ∀ q : UnitTwoSphere, g q = unitRadialProjection p (Q (q : E3))) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0 : ℝ × ℝ) ∈ U ∧
      ContDiffOn ℝ ∞ (fun y => spherePlaneChart (-p)
        (g ((spherePlaneChart (-p)).symm y))) U ∧
      spherePlaneChart (-p) (g ((spherePlaneChart (-p)).symm 0)) = 0 ∧
      fderiv ℝ (fun y => spherePlaneChart (-p)
        (g ((spherePlaneChart (-p)).symm y))) 0 =
          ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  let T := spherePlaneChart (-p)
  have hps : p ∈ T.source := by
    simpa only [T, spherePlaneChart_source, mem_compl_iff, mem_singleton_iff] using
      ne_neg_of_mem_unit_sphere ℝ p
  have hg : g p = p := by rw [hgQ, hQp, unitRadialProjection_apply_coe]
  have hT0 : T p = 0 := spherePlaneChart_neg_apply p
  have hI0 : T.symm 0 = p := spherePlaneChart_neg_symm_zero p
  let h : (ℝ × ℝ) → (ℝ × ℝ) := fun y => T (g (T.symm y))
  let U := (fun y => g (T.symm y)) ⁻¹' T.source
  have hU : IsOpen U := T.open_source.preimage
    (g.continuous.comp (contMDiff_spherePlaneChart_symm (-p)).continuous)
  have h0 : (0 : ℝ × ℝ) ∈ U := by
    change g (T.symm 0) ∈ T.source
    rw [hI0, hg]
    exact hps
  have hh : ContDiffOn ℝ ∞ h U := by
    intro y hy
    have hout := (contMDiffOn_spherePlaneChart (-p)).contMDiffAt
      (T.open_source.mem_nhds hy)
    exact (hout.comp y (g.contMDiff.contMDiffAt.comp y
      (contMDiff_spherePlaneChart_symm (-p)).contMDiffAt)).contDiffAt.contDiffWithinAt
  have hh0 : h 0 = 0 := by simp only [h, hI0, hg, hT0]
  let σ : (ℝ × ℝ) → E3 := fun y => (T.symm y : E3)
  let τ : E3 → (ℝ × ℝ) := fun x => T (unitRadialProjection p x)
  have hσ : ContDiff ℝ ∞ σ :=
    ((contMDiff_coe_sphere (n := 2) (m := ∞)).comp
      (contMDiff_spherePlaneChart_symm (-p))).contDiff
  have hσ0 : σ 0 = (p : E3) := congrArg Subtype.val hI0
  have hτ : ContDiffAt ℝ ∞ τ (p : E3) := by
    have hπ := (contMDiffOn_unitRadialProjection (n := 2) (m := ∞) p).contMDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds
        (show (p : E3) ∈ ({0} : Set E3)ᶜ from ne_zero_of_mem_unit_sphere p))
    have hchart := (contMDiffOn_spherePlaneChart (-p)).contMDiffAt
      (T.open_source.mem_nhds hps)
    have hchart' : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ T
        (unitRadialProjection p (p : E3)) := by
      rw [unitRadialProjection_apply_coe]
      exact hchart
    exact (hchart'.comp (p : E3) hπ).contDiffAt
  have hcanc : τ ∘ σ = id := by
    funext y
    change T (unitRadialProjection p (T.symm y : E3)) = y
    rw [unitRadialProjection_apply_coe]
    exact T.right_inv (spherePlaneChart_target (-p) ▸ mem_univ y)
  have hdσ : DifferentiableAt ℝ σ 0 := hσ.differentiable (by simp) 0
  have hdτ : DifferentiableAt ℝ τ (p : E3) := hτ.differentiableAt (by simp)
  have hcancel : (fderiv ℝ τ (p : E3)).comp (fderiv ℝ σ 0) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [← hσ0, ← fderiv_comp 0 (hσ0.symm ▸ hdτ) hdσ, hcanc, fderiv_id]
  have hrep : h = τ ∘ Q ∘ σ := by
    funext y
    change T (g (T.symm y)) = T (unitRadialProjection p (Q (T.symm y : E3)))
    rw [hgQ]
  have hderiv : fderiv ℝ h 0 = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [hrep, fderiv_comp 0]
    · rw [fderiv_comp 0 (hσ0.symm ▸ hQ) hdσ, comp_apply, hσ0, hQp, hDQ,
        ContinuousLinearMap.id_comp, hcancel]
    · simpa only [comp_apply, hσ0, hQp] using hdτ
    · exact (hσ0.symm ▸ hQ).comp 0 hdσ
  exact ⟨U, hU, h0, hh, hh0, hderiv⟩

end PoincareConjecture.M25.Topology3D
