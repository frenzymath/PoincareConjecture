import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondRadiusMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrismEndpointOrder
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.PrescribedAxisRestriction

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_signed_endpoint_half_face_maps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A Z : Set E} (center : Bool → E) (corner : Bool → Fin 2 → Bool → E)
    (target : Bool → Set E) (rad : Bool → Fin 2 → Bool → Set E)
    (face outer : Fin 2 → Bool → Set E)
    (b : Icc (0 : ℝ) 1 ≃ₜ A) (hb : b.IsFinitePL)
    (hZ : IsFinitePLBallPair ℝ Z {center false, center true})
    (hZA : Z ⊆ A) (hne : center false ≠ center true)
    (hface : ∀ i sign, IsFinitePLBallPair (ℝ × ℝ) (face i sign) (Z ∪ outer i sign))
    (houter : ∀ i sign, IsFinitePLBallPair ℝ (outer i sign) {center false, center true})
    (hcontact : ∀ i sign, Z ∩ outer i sign = {center false, center true})
    (hrad : ∀ j i sign, IsFinitePLBallPair ℝ (rad j i sign) {center j, corner j i sign})
    (hRadOuter : ∀ j i sign, rad j i sign ⊆ outer i sign)
    (hRadTarget : ∀ j i sign, rad j i sign ⊆ target j)
    (hcorner : ∀ j i sign, center j ≠ corner j i sign)
    (hdis : ∀ i sign, Disjoint (rad false i sign) (rad true i sign))
    (G : ∀ j, signedTubeDiamond ≃ₜ target j) (hG : ∀ j, (G j).IsFinitePL)
    (hGradius : ∀ j i sign (x : signedTubeDiamond),
      (x : ℝ × ℝ) ∈ signedTubeRadius i sign ↔ (G j x : E) ∈ rad j i sign)
    (hGcenter : ∀ j, (G j ⟨(0, 0),
      signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ : E) = center j)
    (hGcorner : ∀ j i sign, (G j ⟨signedTubeCorner i sign,
      signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E) = corner j i sign) :
    ∃ (α β : Icc (0 : ℝ) 1) (hlt : α < β)
      (hsub : Icc (α : ℝ) (β : ℝ) ⊆ Icc (0 : ℝ) 1)
      (axis : Icc (α : ℝ) (β : ℝ) ≃ₜ Z) (reverseEnds : Bool),
      let index := fun j : Bool => if reverseEnds then !j else j
      axis.IsFinitePL ∧
      (∀ t, (axis t : E) = (b ⟨t, hsub t.property⟩ : E)) ∧
      (∀ j, (axis ⟨if j then (β : ℝ) else (α : ℝ),
        by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) = center (index j)) ∧
      ∀ i sign, ∃ H : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)) ≃ₜ face i sign,
        H.IsFinitePL ∧
        (∀ t : Icc (α : ℝ) (β : ℝ),
          (H ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) =
            b ⟨t, hsub t.property⟩) ∧
        (∀ j (x : signedTubeRadius i sign),
          (H ⟨(x, if j then (β : ℝ) else (α : ℝ)), x.property,
            by cases j <;> simp [show (α : ℝ) ≤ β from hlt.le]⟩ : E) =
              G (index j) ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : (ℝ × ℝ) × ℝ) ∈ signedTubePrismAxis α β ↔ (H x : E) ∈ Z) ∧
        (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc (α : ℝ) (β : ℝ)),
          (x : (ℝ × ℝ) × ℝ) ∈ signedTubePrismOuter i sign α β ↔ (H x : E) ∈ outer i sign) := by
  classical
  obtain ⟨α, β, hsub, axis, hlt, hends, haxis, haxisval⟩ :=
    exists_prescribed_axis_restriction b hb hZ hZA hne
  have haxisEnds : ({(axis ⟨α, le_rfl, hlt.le⟩ : E),
      (axis ⟨β, hlt.le, le_rfl⟩ : E)} : Set E) = {center false, center true} := by
    rw [haxisval, haxisval]
    exact hends
  choose er her hkeep using fun j i sign =>
    exists_signed_diamond_radius_restriction (G j) (hG j) i sign
      (hRadTarget j i sign) (hGradius j i sign)
  have herCenter (j : Bool) (i : Fin 2) (sign : Bool) :
      (er j i sign ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) = center j :=
    (hkeep j i sign _).trans (hGcenter j)
  have herCorner (j : Bool) (i : Fin 2) (sign : Bool) :
      (er j i sign ⟨signedTubeCorner i sign, right_mem_segment ℝ _ _⟩ : E) = corner j i sign :=
    (hkeep j i sign _).trans (hGcorner j i sign)
  have hConstruct (i : Fin 2) (sign : Bool) :=
    exists_signed_radius_prism_map_in_axis_order i sign α β hlt
      (fun j => rad j i sign) center (fun j => corner j i sign)
      (hface i sign) hZ (houter i sign) (hcontact i sign)
      (fun j => hrad j i sign) (fun j => hRadOuter j i sign) hne
      (fun j => hcorner j i sign) (hdis i sign) axis haxis haxisEnds
      (fun j => er j i sign) (fun j => her j i sign)
      (fun j => herCenter j i sign) (fun j => herCorner j i sign)
  obtain ⟨reverseEnds, H0, hH0, horder0, _⟩ := hConstruct 0 false
  refine ⟨α, β, hlt, hsub, axis, reverseEnds, haxis, haxisval, horder0, ?_⟩
  intro i sign
  obtain ⟨rev, H, hH, horder, hAxisKeep, hEndKeep, hAxisMem, hOuterMem, _⟩ := hConstruct i sign
  have heq : rev = reverseEnds := by
    have h := (horder false).symm.trans (horder0 false)
    cases rev <;> cases reverseEnds
    · rfl
    · exact False.elim (hne h)
    · exact False.elim (hne h.symm)
    · rfl
  subst rev
  exact ⟨H, hH,
    fun t => (hAxisKeep t).trans (haxisval t),
    fun j x => (hEndKeep j x).trans (hkeep _ i sign x), hAxisMem, hOuterMem⟩

end PoincareConjecture.M76.Dehn
