import PoincareConjecture.Proofs.M25.Topology3D.Sphere2.OrthogonalAction
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialCalculus










set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private instance sphereDimensionFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩



noncomputable def linearSphereDiffeomorph (q0 : UnitTwoSphere) (L : E3 ≃L[ℝ] E3) :
    UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere := by
  let F (K : E3 ≃L[ℝ] E3) (q : UnitTwoSphere) := unitRadialProjection q0 (K (q : E3))
  have hn (K : E3 ≃L[ℝ] E3) (q : UnitTwoSphere) : K (q : E3) ≠ 0 :=
    K.injective.ne (ne_zero_of_mem_unit_sphere q) |>.trans_eq (map_zero K)
  have hs (K : E3 ≃L[ℝ] E3) : ContMDiff (𝓡 2) (𝓡 2) ∞ (F K) := by
    have hK : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (fun q : UnitTwoSphere => K (q : E3)) :=
      K.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := 2) (m := ∞))
    intro q
    have hπ := (contMDiffOn_unitRadialProjection (n := 2) (m := ∞) q0).contMDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds (show K (q : E3) ∈ ({0} : Set E3)ᶜ from hn K q))
    exact hπ.comp q hK.contMDiffAt
  have hi (K : E3 ≃L[ℝ] E3) : LeftInverse (F K.symm) (F K) := by
    intro q
    change unitRadialProjection q0 (K.symm (unitRadialProjection q0 (K (q : E3)) : E3)) = q
    rw [unitRadialProjection_coe_of_ne_zero q0 (hn K q), map_smul, K.symm_apply_apply,
      unitRadialProjection_pos_smul q0 (inv_pos.mpr (norm_pos_iff.mpr (hn K q))),
      unitRadialProjection_apply_coe]
  exact
    { toEquiv :=
        { toFun := F L
          invFun := F L.symm
          left_inv := hi L
          right_inv := hi L.symm }
      contMDiff_toFun := hs L
      contMDiff_invFun := hs L.symm }



@[simp] theorem linearSphereDiffeomorph_apply (q0 q : UnitTwoSphere) (L : E3 ≃L[ℝ] E3) :
    linearSphereDiffeomorph q0 L q = unitRadialProjection q0 (L (q : E3)) := rfl



@[simp] theorem linearSphereDiffeomorph_symm_apply (q0 q : UnitTwoSphere)
    (L : E3 ≃L[ℝ] E3) :
    (linearSphereDiffeomorph q0 L).symm q = unitRadialProjection q0 (L.symm (q : E3)) := rfl



theorem linearSphereDiffeomorph_isometry_apply (q0 q : UnitTwoSphere)
    (A : E3 ≃ₗᵢ[ℝ] E3) :
    linearSphereDiffeomorph q0 A.toContinuousLinearEquiv q = sphereMap A q := by
  apply Subtype.ext
  change (unitRadialProjection q0 (A (q : E3)) : E3) = A (q : E3)
  have hn : A (q : E3) ≠ 0 :=
    A.injective.ne (ne_zero_of_mem_unit_sphere q) |>.trans_eq (map_zero A)
  rw [unitRadialProjection_coe_of_ne_zero q0 hn, A.norm_map,
    norm_eq_of_mem_sphere q, inv_one, one_smul]



theorem contMDiff_linearSphereDiffeomorph_family (q0 : UnitTwoSphere)
    (L : ℝ → E3 ≃L[ℝ] E3)
    (hL : ContDiff ℝ ∞ (fun p : ℝ × E3 => L p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × UnitTwoSphere => linearSphereDiffeomorph q0 (L p.1) p.2) := by
  have hinner : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
      (fun p : ℝ × UnitTwoSphere => L p.1 (p.2 : E3)) :=
    hL.contMDiff.comp (contMDiff_fst.prodMk_space
      ((contMDiff_coe_sphere (n := 2) (m := ∞)).comp contMDiff_snd))
  intro p
  have hn : L p.1 (p.2 : E3) ≠ 0 :=
    (L p.1).injective.ne (ne_zero_of_mem_unit_sphere p.2) |>.trans_eq (map_zero (L p.1))
  have hπ := (contMDiffOn_unitRadialProjection (n := 2) (m := ∞) q0).contMDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds
      (show L p.1 (p.2 : E3) ∈ ({0} : Set E3)ᶜ from hn))
  exact hπ.comp p hinner.contMDiffAt

end PoincareConjecture.M25.Topology3D
