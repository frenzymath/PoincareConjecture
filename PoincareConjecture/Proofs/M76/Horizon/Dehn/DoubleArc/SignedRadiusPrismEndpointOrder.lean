import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedRadiusPrismMaps








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

theorem exists_signed_radius_prism_map_in_axis_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin 2) (sign : Bool) (α β : ℝ) (hαβ : α < β)
    {F Axis Outer : Set E} (D : Bool → Set E) (A C : Bool → E)
    (hF : IsFinitePLBallPair (ℝ × ℝ) F (Axis ∪ Outer))
    (hAxis : IsFinitePLBallPair ℝ Axis {A false, A true})
    (hOuter : IsFinitePLBallPair ℝ Outer {A false, A true})
    (hInter : Axis ∩ Outer = {A false, A true})
    (hD : ∀ j, IsFinitePLBallPair ℝ (D j) {A j, C j})
    (hDO : ∀ j, D j ⊆ Outer)
    (hA : A false ≠ A true) (hAC : ∀ j, A j ≠ C j)
    (hDis : Disjoint (D false) (D true))
    (z : Icc α β ≃ₜ Axis) (hz : z.IsFinitePL)
    (hzEnds : ({(z ⟨α, le_rfl, hαβ.le⟩ : E), (z ⟨β, hαβ.le, le_rfl⟩ : E)} : Set E) =
      {A false, A true})
    (e : ∀ j, signedTubeRadius i sign ≃ₜ D j)
    (he : ∀ j, (e j).IsFinitePL)
    (hea : ∀ j, (e j ⟨(0, 0), left_mem_segment ℝ _ _⟩ : E) = A j)
    (hec : ∀ j, (e j ⟨signedTubeCorner i sign, right_mem_segment ℝ _ _⟩ : E) = C j) :
    ∃ (reverseEnds : Bool) (H : ↥(signedTubeRadius i sign ×ˢ Icc α β) ≃ₜ F),
      let index := fun j : Bool => if reverseEnds then !j else j
      H.IsFinitePL ∧
      (∀ j, (z ⟨if j then β else α, by cases j <;> simp [hαβ.le]⟩ : E) = A (index j)) ∧
      (∀ t : Icc α β,
        (H ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t) ∧
      (∀ j (x : signedTubeRadius i sign),
        (H ⟨(x, if j then β else α), x.property,
          by cases j <;> simp [hαβ.le]⟩ : E) = e (index j) x) ∧
      (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc α β),
        (x : (ℝ × ℝ) × ℝ) ∈ signedTubePrismAxis α β ↔ (H x : E) ∈ Axis) ∧
      (∀ x : ↥(signedTubeRadius i sign ×ˢ Icc α β),
        (x : (ℝ × ℝ) × ℝ) ∈ signedTubePrismOuter i sign α β ↔ (H x : E) ∈ Outer) ∧
      ∀ j (x : ↥(signedTubeRadius i sign ×ˢ Icc α β)),
        (x : (ℝ × ℝ) × ℝ) ∈ signedTubeRadius i sign ×ˢ {if j then β else α} ↔
          (H x : E) ∈ D (index j) := by
  rcases pair_eq_pair_iff.mp hzEnds with hEnds | hEnds
  · obtain ⟨H, hH, hAxisKeep, hEndKeep, hAxisMem, hOuterMem, hEndMem⟩ :=
      exists_signed_radius_prism_map i sign α β hαβ D A C hF hAxis hOuter hInter
        hD hDO hA hAC hDis z hz hEnds.1 hEnds.2 e he hea hec
    refine ⟨false, H, hH, ?_, hAxisKeep, hEndKeep, hAxisMem, hOuterMem, hEndMem⟩
    intro j
    cases j
    · exact hEnds.1
    · exact hEnds.2
  · have hAxis' : IsFinitePLBallPair ℝ Axis {A true, A false} := by
      simpa only [pair_comm] using hAxis
    have hOuter' : IsFinitePLBallPair ℝ Outer {A true, A false} := by
      simpa only [pair_comm] using hOuter
    have hInter' : Axis ∩ Outer = {A true, A false} := by
      simpa only [pair_comm] using hInter
    obtain ⟨H, hH, hAxisKeep, hEndKeep, hAxisMem, hOuterMem, hEndMem⟩ :=
      exists_signed_radius_prism_map i sign α β hαβ (fun j => D (!j))
        (fun j => A (!j)) (fun j => C (!j)) hF hAxis' hOuter' hInter'
        (fun j => hD (!j)) (fun j => hDO (!j)) hA.symm (fun j => hAC (!j)) hDis.symm
        z hz hEnds.1 hEnds.2 (fun j => e (!j)) (fun j => he (!j))
        (fun j => hea (!j)) (fun j => hec (!j))
    refine ⟨true, H, hH, ?_, hAxisKeep, hEndKeep, hAxisMem, hOuterMem, hEndMem⟩
    intro j
    cases j
    · exact hEnds.1
    · exact hEnds.2

end PoincareConjecture.M76.Dehn
