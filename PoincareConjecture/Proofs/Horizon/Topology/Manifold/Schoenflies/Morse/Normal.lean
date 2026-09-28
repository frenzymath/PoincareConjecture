import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

open Poincare.LinearAlgebra

theorem exists_smooth_unit_normal
    (f : S2 -> E3) (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ N : S2 -> S2, ContMDiff (𝓡 2) (𝓡 2) ∞ N ∧
      ∀ (p : S2) (w : E3),
        (∀ u, inner Real w (mfderiv (𝓡 2) (𝓡 3) f p u) = 0) ↔
          ∃ c : Real, w = c • (N p : E3) := by
  obtain ⟨G, hG, hrestrict⟩ := exists_contDiff_extension_sphere f hf.contMDiff
  let n : S2 -> E3 := fun p => euclideanCofactorNormal (fderiv Real G p) p
  have hn : ContMDiff (𝓡 2) (𝓡 3) ∞ n :=
    (contDiff_cofactorNormal hG).contMDiff.comp contMDiff_coe_sphere
  have hn0 (p : S2) : n p ≠ 0 := euclideanCofactorNormal_ne_zero _ _ (by simp)
    (injOn_fderiv_extension_tangent_sphere hf hG hrestrict p)
  let N : S2 -> S2 := fun p => ⟨‖n p‖⁻¹ • n p, by
    simp [norm_smul, norm_ne_zero_iff.mpr (hn0 p)]⟩
  have hnorm : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => ‖n p‖) := by
    intro p
    exact (contDiffAt_norm Real (hn0 p)).contMDiffAt.comp p (hn p)
  have hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N :=
    ((hnorm.inv₀ (fun p => norm_ne_zero_iff.mpr (hn0 p))).smul hn).codRestrict_sphere _
  refine ⟨N, hN, ?_⟩
  intro p w
  let L : TangentSpace (𝓡 2) p →L[Real] E3 :=
    mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S2 -> E3) p
  have hrange : L.range = (Real ∙ (p : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal p
  have hchain : mfderiv (𝓡 2) (𝓡 3) f p = (fderiv Real G p).comp L := by
    have heq : f = G ∘ (Subtype.val : S2 -> E3) := funext fun y => (hrestrict y).symm
    rw [heq, mfderiv_comp _ (hG.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (n := 2) p).mdifferentiableAt
        (show (∞ : ℕ∞ω) ≠ 0 by simp)), mfderiv_eq_fderiv]
  have hchain_apply (u) : mfderiv (𝓡 2) (𝓡 3) f p u = fderiv Real G p (L u) :=
    congrArg (fun A : TangentSpace (𝓡 2) p →L[Real] E3 => A u) hchain
  have hL (u) : inner Real (p : E3) (L u) = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← hrange]
    exact ⟨u, rfl⟩
  constructor
  · intro hw
    have ha : ∀ v, inner Real (p : E3) v = 0 -> inner Real w (fderiv Real G p v) = 0 := by
      intro v hv
      have hvL : v ∈ L.range := by
        rw [hrange, Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact hv
      obtain ⟨u, rfl⟩ := hvL
      change inner Real w (fderiv Real G p (L u)) = 0
      rw [← hchain_apply]
      exact hw u
    obtain ⟨c, hc⟩ := (orthogonal_tangent_iff_smul_euclideanCofactorNormal
      (fderiv Real G p) p w (by simp)
      (injOn_fderiv_extension_tangent_sphere hf hG hrestrict p)).mp ha
    refine ⟨c * ‖n p‖, ?_⟩
    change w = (c * ‖n p‖) • (‖n p‖⁻¹ • n p)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hn0 p)), mul_one]
    exact hc
  · rintro ⟨c, rfl⟩ u
    change inner Real (c • (‖n p‖⁻¹ • n p)) _ = 0
    rw [inner_smul_left, inner_smul_left, hchain_apply,
      inner_euclideanCofactorNormal_apply_eq_zero _ _ _ (hL u), mul_zero, mul_zero]

end Poincare.Manifold.Schoenflies
