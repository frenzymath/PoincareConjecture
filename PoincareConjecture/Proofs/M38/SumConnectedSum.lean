import PoincareConjecture.Proofs.M38.SumRegionLifting









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38



noncomputable def sumConnectedSumData {A B C : GeneralizedSliceCarrier.{u}}
    (S : SmoothConnectedSumData A B C) (D : GeneralizedSliceCarrier.{u}) :
    SmoothConnectedSumData (sumCarrier A D) B (sumCarrier C D) := by
  let E := sumInlEquivalence C D ⟨S.first_identify.map (S.first_ball.map 0)⟩
  let E₀ := sumRegionEquivalence D S.first_identify
    (surgeryBall_closedImage_compact S.first_ball 1 (by norm_num)).isClosed.isOpen_compl
    S.first_open
  refine {
    first_ball := sumInlBall S.first_ball D
    second_ball := S.second_ball
    first_region := sumFullRegion D S.first_region
    second_region := Sum.inl '' S.second_region
    first_open := sumFullRegion_open D S.first_open
    second_open := isOpenMap_inl _ S.second_open
    first_identify := {
      map := E₀.map
      inverse := E₀.inverse
      map_image := by rw [sumInlBall_complement]; exact E₀.map_image
      inverse_image := by rw [sumInlBall_complement]; exact E₀.inverse_image
      left_inverse := by rw [sumInlBall_complement]; exact E₀.left_inverse
      right_inverse := E₀.right_inverse
      map_smooth := by rw [sumInlBall_complement]; exact E₀.map_smooth
      inverse_smooth := E₀.inverse_smooth }
    second_identify := composeRegions S.second_identify
      (restrictRegions E S.second_region (Set.subset_univ _))
    regions_disjoint := sumFullRegion_disjoint_inl D S.regions_disjoint
    sphere_gluing := S.sphere_gluing
    collar := Sum.inl ∘ S.collar
    collar_inverse := S.collar_inverse ∘ E.inverse
    collar_smooth := ContMDiff.inl.comp_contMDiffOn S.collar_smooth
    collar_inverse_smooth := ?_
    collar_left_inverse := ?_
    collar_right_inverse := ?_
    collar_open := ?_
    negative_gluing := ?_
    positive_gluing := ?_
    central_disjoint := ?_
    cover := ?_ }
  · apply S.collar_inverse_smooth.comp (E.inverse_smooth.mono ?_) ?_
    · rintro q ⟨z, hz, rfl⟩
      exact Set.mem_range_self _
    · rintro q ⟨z, hz, rfl⟩
      change E.inverse (E.map (S.collar z)) ∈
        S.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
      rw [E.left_inverse (Set.mem_univ _)]
      exact ⟨z, hz, rfl⟩
  · intro z hz
    change S.collar_inverse (E.inverse (E.map (S.collar z))) = z
    rw [E.left_inverse (Set.mem_univ _)]
    exact S.collar_left_inverse hz
  · rintro q ⟨z, hz, rfl⟩
    change Sum.inl (S.collar (S.collar_inverse (E.inverse (E.map (S.collar z))))) =
      Sum.inl (S.collar z)
    rw [E.left_inverse (Set.mem_univ _),
      S.collar_right_inverse (Set.mem_image_of_mem _ hz)]
  · rw [Set.image_comp]
    exact isOpenMap_inl _ S.collar_open
  · intro z s hs
    change Sum.inl (S.collar (z, s)) =
      Sum.inl (S.first_identify.map (S.first_ball.map ((1 - s) • z.val)))
    exact congrArg Sum.inl (S.negative_gluing z s hs)
  · intro z s hs
    change Sum.inl (S.collar (z, s)) =
      Sum.inl (S.second_identify.map
        (S.second_ball.map ((1 + s) • (S.sphere_gluing z).val)))
    exact congrArg Sum.inl (S.positive_gluing z s hs)
  · apply Set.disjoint_left.mpr
    rintro q ⟨z, hz, rfl⟩ ((hfirst | ⟨d, hd⟩) | hsecond)
    · obtain ⟨x, hx, hxeq⟩ := hfirst
      have heq : x = S.collar z := Sum.inl_injective hxeq
      exact Set.disjoint_left.mp S.central_disjoint ⟨z, hz, rfl⟩ (Or.inl (heq ▸ hx))
    · cases hd
    · obtain ⟨x, hx, hxeq⟩ := hsecond
      have heq : x = S.collar z := Sum.inl_injective hxeq
      exact Set.disjoint_left.mp S.central_disjoint ⟨z, hz, rfl⟩ (Or.inr (heq ▸ hx))
  · apply Set.eq_univ_of_forall
    intro q
    cases q with
    | inl x =>
        have hx : x ∈ S.first_region ∪ S.second_region ∪
            S.collar '' (Set.univ ×ˢ ({0} : Set ℝ)) := S.cover.symm ▸ Set.mem_univ x
        rcases hx with (hx | hx) | ⟨z, hz, rfl⟩
        · exact Or.inl (Or.inl (Or.inl ⟨x, hx, rfl⟩))
        · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
        · exact Or.inr ⟨z, hz, rfl⟩
    | inr x => exact Or.inl (Or.inl (Or.inr (Set.mem_range_self x)))


noncomputable def sumTwoPieceUnion {A B C : GeneralizedSliceCarrier.{u}}
    (U : SmoothDisjointUnionData ![A, B] C) (D : GeneralizedSliceCarrier.{u})
    (hC : Nonempty C.carrier) :
    SmoothDisjointUnionData ![sumCarrier A D, B] (sumCarrier C D) := by
  let E := sumInlEquivalence C D hC
  let E₀ := sumRegionEquivalence D (U.identify 0) isOpen_univ (U.region_open 0)
  let E₁ := composeRegions (U.identify 1)
    (restrictRegions E (U.region 1) (Set.subset_univ _))
  have hfull : sumFullRegion D (Set.univ : Set A.carrier) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    cases q with
    | inl x => exact Or.inl ⟨x, Set.mem_univ x, rfl⟩
    | inr x => exact Or.inr (Set.mem_range_self x)
  let F₀ : SurgeryRegionEquivalence (sumCarrier A D) (sumCarrier C D) Set.univ
      (sumFullRegion D (U.region 0)) := {
    map := E₀.map
    inverse := E₀.inverse
    map_image := by rw [← hfull]; exact E₀.map_image
    inverse_image := by rw [← hfull]; exact E₀.inverse_image
    left_inverse := by rw [← hfull]; exact E₀.left_inverse
    right_inverse := E₀.right_inverse
    map_smooth := by rw [← hfull]; exact E₀.map_smooth
    inverse_smooth := E₀.inverse_smooth }
  have hdis : Disjoint (sumFullRegion D (U.region 0)) (Sum.inl '' U.region 1) :=
    sumFullRegion_disjoint_inl D (U.pairwise_disjoint 0 1 (by decide))
  refine {
    region := ![sumFullRegion D (U.region 0), Sum.inl '' U.region 1]
    region_open := ?_
    region_closed := ?_
    identify := fun i => Fin.cases F₀
      (fun j => Fin.cases E₁ (fun k => Fin.elim0 k) j) i
    pairwise_disjoint := ?_
    cover := ?_ }
  · intro i
    fin_cases i
    · exact sumFullRegion_open D (U.region_open 0)
    · exact isOpenMap_inl _ (U.region_open 1)
  · intro i
    fin_cases i
    · exact sumFullRegion_closed D (U.region_closed 0)
    · exact isClosedMap_inl _ (U.region_closed 1)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  · apply Set.eq_univ_of_forall
    intro q
    cases q with
    | inl x =>
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (U.cover.symm ▸ Set.mem_univ x)
        fin_cases i
        · exact Set.mem_iUnion.mpr ⟨0, Or.inl ⟨x, hi, rfl⟩⟩
        · exact Set.mem_iUnion.mpr ⟨1, ⟨x, hi, rfl⟩⟩
    | inr x => exact Set.mem_iUnion.mpr ⟨0, Or.inr (Set.mem_range_self x)⟩


theorem sumConnectedSumStep {A C : GeneralizedSliceCarrier.{u}}
    (h : SmoothConnectedSumStep A C) (D : GeneralizedSliceCarrier.{u}) :
    SmoothConnectedSumStep (sumCarrier A D) (sumCarrier C D) := by
  obtain ⟨B, E, ⟨U⟩, ⟨S⟩⟩ := h
  have hA : Nonempty A.carrier := ⟨(U.identify 0).map (S.first_ball.map 0)⟩
  exact ⟨sumCarrier B D, E, ⟨sumTwoPieceUnion U D hA⟩, ⟨sumConnectedSumData S D⟩⟩


theorem sumConnectedSumChain {A C : GeneralizedSliceCarrier.{u}}
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) (D : GeneralizedSliceCarrier.{u}) :
    Relation.ReflTransGen SmoothConnectedSumStep (sumCarrier A D) (sumCarrier C D) := by
  induction h with
  | refl => exact .refl
  | tail h hstep ih => exact ih.tail (sumConnectedSumStep hstep D)

end PoincareConjecture.M38
