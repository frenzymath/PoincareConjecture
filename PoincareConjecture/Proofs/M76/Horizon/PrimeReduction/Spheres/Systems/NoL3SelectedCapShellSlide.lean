import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapProductSlide
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) (1/8)
local notation "J" => Icc (-(1/32 : ℝ)) (1/32)
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7/8) 1
local notation "D" => (norm : V3 → ℝ) ⁻¹' Icc (29/32) (31/32)

theorem exists_selected_cap_shell_slide
    (Q : (Sphere ×ˢ I : Set (V3 × ℝ)) ≃ₜ T) (hQ : Q.IsFinitePL)
    (hQnorm : ∀ z : (Sphere ×ˢ I : Set (V3 × ℝ)),
      ‖(Q z : V3)‖ = 1-(z : V3 × ℝ).2) :
    ∃ (P : (Sphere ×ˢ J : Set (V3 × ℝ)) ≃ₜ D) (H : D ≃ₜ D),
      P.IsFinitePL ∧ H.IsFinitePL ∧ D ⊆ interior T ∧
      (∀ x : D, (x : V3) ∈ frontier D → H x = x) ∧
      (∀ z : (Sphere ×ˢ J : Set (V3 × ℝ)),
        (P z : V3) = Q ⟨((z : V3 × ℝ).1,(z : V3 × ℝ).2+1/16),
          z.property.1,by constructor <;> linarith [z.property.2.1,z.property.2.2]⟩) ∧
      (∀ z : (Sphere ×ˢ J : Set (V3 × ℝ)),
        (P.symm (H (P z)) : V3 × ℝ).1 = (z : V3 × ℝ).1 ∧
        (P.symm (H (P z)) : V3 × ℝ).2 =
          if (z : V3 × ℝ).2 ≤ 0 then (3*(z : V3 × ℝ).2+1/32)/2
          else ((z : V3 × ℝ).2+1/32)/2) := by
  let J' := Icc (1/32 : ℝ) (3/32)
  let A : J ≃ₜ J' := {
    toFun := fun t => ⟨(t : ℝ)+1/16,by constructor <;> linarith [t.property.1,t.property.2]⟩
    invFun := fun t => ⟨(t : ℝ)-1/16,by constructor <;> linarith [t.property.1,t.property.2]⟩
    left_inv := by intro t; apply Subtype.ext; dsimp; ring
    right_inv := by intro t; apply Subtype.ext; dsimp; ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show -(1/32 : ℝ) < 1/32 by norm_num)
  let a : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ + ContinuousAffineMap.const ℝ ℝ (1/16)
  have hA : A.IsFinitePL :=
    ⟨a,⟨L,hL,hLs,L.affineOnFaces_affine a⟩,fun _ => rfl⟩
  obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hid : (Homeomorph.refl Sphere).IsFinitePL :=
    ⟨id,⟨K,hK,hKs,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)⟩,fun _ => rfl⟩
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L',hL',hLs',_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (1/32 : ℝ) < 3/32 by norm_num)
  obtain ⟨M,hM,hMs,_⟩ := K.exists_finite_triangulation_prod L' hK hL'
  have hMs' : M.space = Sphere ×ˢ J' := by simpa only [hKs,hLs',J'] using hMs
  have hsub : Sphere ×ˢ J' ⊆ Sphere ×ˢ I :=
    fun _ hz => ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  have hDT : D ⊆ T := fun _ hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hmem (z : (Sphere ×ˢ I : Set (V3 × ℝ))) :
      (z : V3 × ℝ) ∈ Sphere ×ˢ J' ↔ (Q z : V3) ∈ D := by
    change ((z : V3 × ℝ).1 ∈ Sphere ∧ (z : V3 × ℝ).2 ∈ J') ↔
      29/32 ≤ ‖(Q z : V3)‖ ∧ ‖(Q z : V3)‖ ≤ 31/32
    rw [hQnorm]
    constructor
    · rintro ⟨_,hz⟩
      constructor <;> linarith [hz.1,hz.2]
    · intro hz
      refine ⟨z.property.1,?_,?_⟩ <;> linarith [hz.1,hz.2]
  let Q' := Q.restrictSubsets hsub hDT hmem
  have hQ' : Q'.IsFinitePL := hQ.restrictSubsets hsub hDT hmem M hM hMs'
  let P := ((Homeomorph.Set.prod Sphere J).trans
    (((Homeomorph.refl Sphere).prodCongr A).trans (Homeomorph.Set.prod Sphere J').symm)).trans Q'
  have hP : P.IsFinitePL := (hid.prod hA).trans hQ'
  have hPval (z : (Sphere ×ˢ J : Set (V3 × ℝ))) :
      (P z : V3) = Q ⟨((z : V3 × ℝ).1,(z : V3 × ℝ).2+1/16),
        z.property.1,by constructor <;> linarith [z.property.2.1,z.property.2.2]⟩ := rfl
  have hPnorm (z : (Sphere ×ˢ J : Set (V3 × ℝ))) :
      ‖(P z : V3)‖ = 15/16-(z : V3 × ℝ).2 := by rw [hPval,hQnorm]; ring
  have hDclosed : IsClosed D := isClosed_Icc.preimage continuous_norm
  have hfront (x : D) (hx : (x : V3) ∈ frontier D) :
      (P.symm x : V3 × ℝ).2 = -(1/32) ∨ (P.symm x : V3 × ℝ).2 = 1/32 := by
    have hn := hPnorm (P.symm x)
    rw [P.apply_symm_apply] at hn
    have hnorm : ‖(x : V3)‖ = 29/32 ∨ ‖(x : V3)‖ = 31/32 := by
      by_contra h
      push Not at h
      have hxin : (x : V3) ∈ (norm : V3 → ℝ) ⁻¹' Ioo (29/32) (31/32) :=
        ⟨lt_of_le_of_ne x.property.1 (Ne.symm h.1),lt_of_le_of_ne x.property.2 h.2⟩
      exact hx.2 (((isOpen_Ioo.preimage continuous_norm).subset_interior_iff.mpr
        (show (norm : V3 → ℝ) ⁻¹' Ioo (29/32) (31/32) ⊆ D from
          fun _ hz => ⟨hz.1.le,hz.2.le⟩)) hxin)
    rcases hnorm with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  let P' := (Homeomorph.setCongr (congrArg (fun A : Set V3 => A ×ˢ J) hKs)).trans P
  have hP' : P'.IsFinitePL := hP.setCongr (congrArg (fun A : Set V3 => A ×ˢ J) hKs).symm rfl
  obtain ⟨H,hH,hfix,hmove,_⟩ := exists_selected_cap_product_slide K hK
    (by norm_num : (0 : ℝ) < 1/32) P' hP' hfront
  refine ⟨P,H,hP,hH,?_,hfix,hPval,?_⟩
  · intro x hx
    apply (isOpen_Ioo.preimage continuous_norm).subset_interior_iff.mpr
      (show (norm : V3 → ℝ) ⁻¹' Ioo (7/8) 1 ⊆ T from fun _ hz => ⟨hz.1.le,hz.2.le⟩)
    constructor <;> linarith [hx.1,hx.2]
  · intro z
    exact hmove ⟨z,hKs.symm.subset z.property.1,z.property.2⟩

end PoincareConjecture.M76
