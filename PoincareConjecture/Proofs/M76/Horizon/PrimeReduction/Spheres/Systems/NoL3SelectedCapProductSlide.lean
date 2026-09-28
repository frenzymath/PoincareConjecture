import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3SelectedCapIntervalSlide
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_selected_cap_product_slide
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {C : Set F} {ε : ℝ} (hε : 0 < ε)
    (Q : (K.space ×ˢ Icc (-ε) ε : Set (E × ℝ)) ≃ₜ C) (hQ : Q.IsFinitePL)
    (hfront : ∀ x : C, (x : F) ∈ frontier C →
      (Q.symm x : E × ℝ).2 = -ε ∨ (Q.symm x : E × ℝ).2 = ε) :
    ∃ H : C ≃ₜ C, H.IsFinitePL ∧
      (∀ x : C, (x : F) ∈ frontier C → H x = x) ∧
      (∀ z : (K.space ×ˢ Icc (-ε) ε : Set (E × ℝ)),
        (Q.symm (H (Q z)) : E × ℝ).1 = (z : E × ℝ).1 ∧
        (Q.symm (H (Q z)) : E × ℝ).2 =
          if (z : E × ℝ).2 ≤ 0 then (3*(z : E × ℝ).2+ε)/2
          else ((z : E × ℝ).2+ε)/2) ∧
      ∀ x : C, (Q.symm (H x) : E × ℝ).2 ≤ ε/2 ↔ (Q.symm x : E × ℝ).2 ≤ 0 := by
  obtain ⟨T,hT,hTv,hTneg,hTpos,_,hTside⟩ := exists_selected_cap_interval_slide hε
  let P := (Homeomorph.Set.prod K.space (Icc (-ε) ε)).trans
    (((Homeomorph.refl K.space).prodCongr T).trans
      (Homeomorph.Set.prod K.space (Icc (-ε) ε)).symm)
  have hid : (Homeomorph.refl K.space).IsFinitePL :=
    ⟨id,⟨K,hK,rfl,K.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩,fun _ => rfl⟩
  have hP : P.IsFinitePL := hid.prod hT
  let H := Q.symm.trans (P.trans Q)
  have hval (z : (K.space ×ˢ Icc (-ε) ε : Set (E × ℝ))) :
      Q.symm (H (Q z)) = P z := by
    change Q.symm (Q (P (Q.symm (Q z)))) = P z
    rw [Q.symm_apply_apply,Q.symm_apply_apply]
  refine ⟨H,hQ.symm.trans (hP.trans hQ),?_,?_,?_⟩
  · intro x hx
    have hp : P (Q.symm x) = Q.symm x := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      change (T ⟨(Q.symm x : E × ℝ).2,(Q.symm x).property.2⟩ : ℝ) = (Q.symm x : E × ℝ).2
      rcases hfront x hx with h | h
      · have hz : (⟨(Q.symm x : E × ℝ).2,(Q.symm x).property.2⟩ : Icc (-ε) ε) =
            ⟨-ε,by constructor <;> linarith⟩ := Subtype.ext h
        rw [hz,hTneg,h]
      · have hz : (⟨(Q.symm x : E × ℝ).2,(Q.symm x).property.2⟩ : Icc (-ε) ε) =
            ⟨ε,by constructor <;> linarith⟩ := Subtype.ext h
        rw [hz,hTpos,h]
    change Q (P (Q.symm x)) = x
    rw [hp,Q.apply_symm_apply]
  · intro z
    rw [hval]
    exact ⟨rfl,hTv ⟨(z : E × ℝ).2,z.property.2⟩⟩
  · intro x
    have h := hval (Q.symm x)
    rw [Q.apply_symm_apply] at h
    rw [h]
    exact hTside ⟨(Q.symm x : E × ℝ).2,(Q.symm x).property.2⟩

end PoincareConjecture.M76
