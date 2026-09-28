import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Proofs.M38.AssemblyCombinators
import PoincareConjecture.Proofs.M38.OneCapReconstruction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

noncomputable def sumCarrier (B D : GeneralizedSliceCarrier.{u}) :
    GeneralizedSliceCarrier.{u} := by
  letI : MeasurableSpace (B.carrier ⊕ D.carrier) :=
    borel (B.carrier ⊕ D.carrier)
  letI : RegularSpace (B.carrier ⊕ D.carrier) := by
    refine RegularSpace.of_hasBasis
      (ι := fun x => match x with
        | .inl _ => Set B.carrier
        | .inr _ => Set D.carrier)
      (p := fun x i => match x with
        | .inl b => i ∈ 𝓝 b ∧ IsClosed i
        | .inr d => i ∈ 𝓝 d ∧ IsClosed i)
      (s := fun x i => match x with
        | .inl _ => Sum.inl '' i
        | .inr _ => Sum.inr '' i) ?_ ?_
    · intro x
      cases x with
      | inl x =>
          rw [nhds_inl]
          exact (closed_nhds_basis x).map
            (Sum.inl : B.carrier → B.carrier ⊕ D.carrier)
      | inr x =>
          rw [nhds_inr]
          exact (closed_nhds_basis x).map
            (Sum.inr : D.carrier → B.carrier ⊕ D.carrier)
    · intro x i hi
      cases x with
      | inl x =>
          rw [isClosed_sum_iff]
          constructor
          · rw [preimage_image_eq _ Sum.inl_injective]
            exact hi.2
          · rw [preimage_inr_image_inl]
            exact isClosed_empty
      | inr x =>
          rw [isClosed_sum_iff]
          constructor
          · rw [preimage_inl_image_inr]
            exact isClosed_empty
          · rw [preimage_image_eq _ Sum.inr_injective]
            exact hi.2
  exact {
    carrier := B.carrier ⊕ D.carrier
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := inferInstance }

noncomputable def sumInlEquivalence (B D : GeneralizedSliceCarrier.{u})
    (hB : Nonempty B.carrier) :
    SurgeryRegionEquivalence B (sumCarrier B D) Set.univ
      (Set.range (Sum.inl : B.carrier → (sumCarrier B D).carrier)) := by
  classical
  let b₀ : B.carrier := Classical.choice hB
  let inverse : (sumCarrier B D).carrier → B.carrier :=
    Sum.elim id (fun _ => b₀)
  refine {
    map := Sum.inl
    inverse := inverse
    map_image := by
      change Sum.inl '' (Set.univ : Set B.carrier) =
        Set.range (Sum.inl : B.carrier → (sumCarrier B D).carrier)
      simp
    inverse_image := ?_
    left_inverse := ?_
    right_inverse := ?_
    map_smooth := ?_
    inverse_smooth := ?_ }
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨Sum.inl x, Set.mem_range_self _, by simp [inverse]⟩
  · intro x _
    rfl
  · rintro _ ⟨x, rfl⟩
    change Sum.inl (inverse (Sum.inl x)) = Sum.inl x
    rfl
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (Sum.inl : B.carrier → (sumCarrier B D).carrier) Set.univ
    exact ContMDiff.inl.contMDiffOn
  · exact (ContMDiff.sumElim contMDiff_id contMDiff_const).contMDiffOn

noncomputable def sumInrEquivalence (B D : GeneralizedSliceCarrier.{u})
    (hD : Nonempty D.carrier) :
    SurgeryRegionEquivalence D (sumCarrier B D) Set.univ
      (Set.range (Sum.inr : D.carrier → (sumCarrier B D).carrier)) := by
  classical
  let d₀ : D.carrier := Classical.choice hD
  let inverse : (sumCarrier B D).carrier → D.carrier :=
    Sum.elim (fun _ => d₀) id
  refine {
    map := Sum.inr
    inverse := inverse
    map_image := by
      change Sum.inr '' (Set.univ : Set D.carrier) =
        Set.range (Sum.inr : D.carrier → (sumCarrier B D).carrier)
      simp
    inverse_image := ?_
    left_inverse := ?_
    right_inverse := ?_
    map_smooth := ?_
    inverse_smooth := ?_ }
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨Sum.inr x, Set.mem_range_self _, by simp [inverse]⟩
  · intro x _
    rfl
  · rintro _ ⟨x, rfl⟩
    change Sum.inr (inverse (Sum.inr x)) = Sum.inr x
    rfl
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (Sum.inr : D.carrier → (sumCarrier B D).carrier) Set.univ
    exact ContMDiff.inr.contMDiffOn
  · exact (ContMDiff.sumElim contMDiff_const contMDiff_id).contMDiffOn

noncomputable def oneCapDisjointUnion (B D : GeneralizedSliceCarrier.{u})
    (hB : Nonempty B.carrier) (hD : Nonempty D.carrier) :
    SmoothDisjointUnionData ![B, D] (sumCarrier B D) := by
  refine {
    region := ![
      Set.range (Sum.inl : B.carrier → (sumCarrier B D).carrier),
      Set.range (Sum.inr : D.carrier → (sumCarrier B D).carrier)]
    region_open := ?_
    region_closed := ?_
    identify := fun i =>
      Fin.cases (sumInlEquivalence B D hB)
        (fun j => Fin.cases (sumInrEquivalence B D hD)
          (fun k => Fin.elim0 k) j) i
    pairwise_disjoint := ?_
    cover := ?_ }
  · intro i
    fin_cases i
    · exact isOpen_range_inl
    · exact isOpen_range_inr
  · intro i
    fin_cases i
    · exact isClosed_range_inl
    · exact isClosed_range_inr
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact Set.isCompl_range_inl_range_inr.disjoint
    · exact Set.isCompl_range_inl_range_inr.symm.disjoint
    · exact (hij rfl).elim
  · apply Set.eq_univ_of_forall
    intro x
    cases x with
    | inl x =>
        exact Set.mem_iUnion.mpr ⟨0, Set.mem_range_self x⟩
    | inr x =>
        exact Set.mem_iUnion.mpr ⟨1, Set.mem_range_self x⟩

theorem exists_one_cap_assembly
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (hcount : (F.event T hT).cap_count = 1) :
    ∃ D : GeneralizedSliceCarrier.{u},
      IsCompact (Set.univ : Set D.carrier) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly
        ![F.slice T, D] (F.slice (F.event T hT).tMinus)) := by
  classical
  obtain ⟨D, hcompact, ⟨S⟩⟩ :=
    exists_one_cap_reconstruction F T hT hcount
  have hB : Nonempty (F.slice T).carrier :=
    ⟨S.first_ball.map 0⟩
  have hD : Nonempty D.carrier :=
    ⟨S.second_ball.map 0⟩
  let A := sumCarrier (F.slice T) D
  let U : SmoothDisjointUnionData ![F.slice T, D] A :=
    oneCapDisjointUnion (F.slice T) D hB hD
  have hstep : SmoothConnectedSumStep A
      (F.slice (F.event T hT).tMinus) :=
    ⟨F.slice T, D, ⟨U⟩, ⟨S⟩⟩
  exact ⟨D, hcompact, ⟨U.toAssembly.tail hstep⟩⟩

end PoincareConjecture.M38
