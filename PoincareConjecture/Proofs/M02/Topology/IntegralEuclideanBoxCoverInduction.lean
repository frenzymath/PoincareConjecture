import PoincareConjecture.Proofs.M02.Topology.IntegralEuclideanDirectedInduction

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe v

namespace PoincareConjecture.Proofs.M02.Topology

private abbrev E := EuclideanSpace Real (Fin 3)

private theorem euclideanOpenCapProperty_congr
    {U V : Set E} (h : U = V) (hU : IsOpen U) (hV : IsOpen V)
    (hprop : integralEuclideanOpenCapProperty U hU) :
    integralEuclideanOpenCapProperty V hV := by
  subst V
  exact hprop

theorem integralEuclideanOpenCapProperty_box_or_empty
    (a b : Fin 3 → Real) :
    integralEuclideanOpenCapProperty (euclideanThreeOpenBox a b)
      (euclideanThreeOpenBox_isOpen a b) := by
  rcases (euclideanThreeOpenBox a b).eq_empty_or_nonempty with h | h
  · exact euclideanOpenCapProperty_congr h.symm isOpen_empty
      (euclideanThreeOpenBox_isOpen a b) integralEuclideanOpenCapProperty_empty
  · exact integralEuclideanOpenCapProperty_box a b h

def euclideanThreeOpenBoxFiniteUnion
    {I : Type v} (s : Finset I) (a b : I → Fin 3 → Real) : Set E :=
  ⋃ i ∈ s, euclideanThreeOpenBox (a i) (b i)

theorem euclideanThreeOpenBoxFiniteUnion_isOpen
    {I : Type v} (s : Finset I) (a b : I → Fin 3 → Real) :
    IsOpen (euclideanThreeOpenBoxFiniteUnion s a b) :=
  isOpen_iUnion fun i => isOpen_iUnion fun _ => euclideanThreeOpenBox_isOpen (a i) (b i)

theorem integralEuclideanOpenCapProperty_finite_box_union
    {I : Type v} (s : Finset I) (a b : I → Fin 3 → Real) :
    integralEuclideanOpenCapProperty (euclideanThreeOpenBoxFiniteUnion s a b)
      (euclideanThreeOpenBoxFiniteUnion_isOpen s a b) := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
      simpa only [euclideanThreeOpenBoxFiniteUnion, Finset.notMem_empty,
        iUnion_of_empty, iUnion_empty] using integralEuclideanOpenCapProperty_empty
  | @insert i s hi ih =>
      let a' : I → Fin 3 → Real := fun j k => max (a i k) (a j k)
      let b' : I → Fin 3 → Real := fun j k => min (b i k) (b j k)
      have hI : euclideanThreeOpenBox (a i) (b i) ∩
          euclideanThreeOpenBoxFiniteUnion s a b =
          euclideanThreeOpenBoxFiniteUnion s a' b' := by
        simp only [euclideanThreeOpenBoxFiniteUnion, inter_iUnion₂,
          euclideanThreeOpenBox_inter, a', b']
      have hIP := euclideanOpenCapProperty_congr hI.symm
        (euclideanThreeOpenBoxFiniteUnion_isOpen s a' b')
        ((euclideanThreeOpenBox_isOpen (a i) (b i)).inter
          (euclideanThreeOpenBoxFiniteUnion_isOpen s a b)) (ih a' b')
      have hP := integralEuclideanOpenCapProperty_union
        (euclideanThreeOpenBox (a i) (b i)) (euclideanThreeOpenBoxFiniteUnion s a b)
        (euclideanThreeOpenBox_isOpen (a i) (b i))
        (euclideanThreeOpenBoxFiniteUnion_isOpen s a b)
        (integralEuclideanOpenCapProperty_box_or_empty (a i) (b i))
        (ih a b) hIP
      have hS : euclideanThreeOpenBox (a i) (b i) ∪
          euclideanThreeOpenBoxFiniteUnion s a b =
          euclideanThreeOpenBoxFiniteUnion (insert i s) a b := by
        simp only [euclideanThreeOpenBoxFiniteUnion, Finset.set_biUnion_insert]
      exact euclideanOpenCapProperty_congr hS _ _ hP

theorem integralEuclideanOpenCapProperty_nonempty_finite_box_intersection
    {I : Type v} (s : Finset I) (hs : s.Nonempty) (a b : I → Fin 3 → Real) :
    integralEuclideanOpenCapProperty (⋂ i ∈ s, euclideanThreeOpenBox (a i) (b i))
      (isOpen_biInter_finset fun i _ => euclideanThreeOpenBox_isOpen (a i) (b i)) := by
  obtain ⟨c, d, h⟩ := euclideanThreeOpenBox_finite_intersection s hs a b
  exact euclideanOpenCapProperty_congr h.symm
    (euclideanThreeOpenBox_isOpen c d) _
    (integralEuclideanOpenCapProperty_box_or_empty c d)

def euclideanThreeBoxesInside (U : Set E) :=
  {p : (Fin 3 → Real) × (Fin 3 → Real) // euclideanThreeOpenBox p.1 p.2 ⊆ U}

def euclideanThreeBoxCoverStage (U : Set E)
    (s : Finset (euclideanThreeBoxesInside U)) : Set E :=
  euclideanThreeOpenBoxFiniteUnion s (fun p => p.1.1) (fun p => p.1.2)

theorem euclideanThreeBoxCoverStage_isOpen (U : Set E)
    (s : Finset (euclideanThreeBoxesInside U)) :
    IsOpen (euclideanThreeBoxCoverStage U s) :=
  euclideanThreeOpenBoxFiniteUnion_isOpen s _ _

theorem euclideanThreeBoxCoverStage_subset (U : Set E)
    (s : Finset (euclideanThreeBoxesInside U)) : euclideanThreeBoxCoverStage U s ⊆ U := by
  rintro x hx
  obtain ⟨p, _, hp⟩ := mem_iUnion₂.mp hx
  exact p.2 hp

theorem euclideanThreeBoxCoverStage_mono (U : Set E)
    {s t : Finset (euclideanThreeBoxesInside U)} (hst : s ⊆ t) :
    euclideanThreeBoxCoverStage U s ⊆ euclideanThreeBoxCoverStage U t := by
  rintro x hx
  obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨p, hst hp, hx⟩

theorem euclideanThreeBoxCoverStage_directed (U : Set E) :
    Directed (fun A B : Set E => A ⊆ B) (euclideanThreeBoxCoverStage U) := by
  classical
  intro s t
  exact ⟨s ∪ t,
    euclideanThreeBoxCoverStage_mono U Finset.subset_union_left,
    euclideanThreeBoxCoverStage_mono U Finset.subset_union_right⟩

theorem euclideanThreeBoxCoverStage_iUnion (U : Set E) (hU : IsOpen U) :
    (⋃ s, euclideanThreeBoxCoverStage U s) = U := by
  classical
  apply Set.Subset.antisymm
  · exact iUnion_subset (euclideanThreeBoxCoverStage_subset U)
  · intro x hx
    obtain ⟨a, b, hxab, habU⟩ := exists_euclideanThreeOpenBox_subset hU hx
    let p : euclideanThreeBoxesInside U := ⟨(a, b), habU⟩
    exact mem_iUnion.mpr ⟨{p}, mem_iUnion₂.mpr ⟨p, Finset.mem_singleton_self p, hxab⟩⟩

theorem integralEuclideanOpenCapProperty_of_isOpen (U : Set E) (hU : IsOpen U) :
    integralEuclideanOpenCapProperty U hU := by
  have hstage : ∀ s, integralEuclideanOpenCapProperty (euclideanThreeBoxCoverStage U s)
      (euclideanThreeBoxCoverStage_isOpen U s) := by
    intro s
    exact integralEuclideanOpenCapProperty_finite_box_union s _ _
  have hP := integralEuclideanOpenCapProperty_directed_union
    (euclideanThreeBoxCoverStage U) (euclideanThreeBoxCoverStage_isOpen U)
    (euclideanThreeBoxCoverStage_directed U) hstage
  exact euclideanOpenCapProperty_congr (euclideanThreeBoxCoverStage_iUnion U hU) _ hU hP

theorem integralEuclideanOpenCapProperty_finite_box_intersection
    {I : Type v} (s : Finset I) (a b : I → Fin 3 → Real) :
    integralEuclideanOpenCapProperty (⋂ i ∈ s, euclideanThreeOpenBox (a i) (b i))
      (isOpen_biInter_finset fun i _ => euclideanThreeOpenBox_isOpen (a i) (b i)) :=
  integralEuclideanOpenCapProperty_of_isOpen _ _

end PoincareConjecture.Proofs.M02.Topology
