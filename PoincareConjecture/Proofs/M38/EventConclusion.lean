import PoincareConjecture.Proofs.M38.ComponentDecomposition
import PoincareConjecture.Proofs.M38.CapCorrespondence
import PoincareConjecture.Proofs.M38.CappingCarrier
import PoincareConjecture.Proofs.M38.MonodromyModel











set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38






noncomputable def eventAssemblyConclusion
    {A B : GeneralizedSliceCarrier.{u}} {m n k : ℕ}
    (rB : Fin m → B.carrier)
    (UB : SmoothDisjointUnionData (fun i => componentCarrier B (rB i)) B)
    (hregionB : ∀ i, UB.region i = connectedComponent (rB i))
    (hB : IsCompact (Set.univ : Set B.carrier))
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (beta : Fin k → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (S : SmoothFiniteConnectedSumAssembly
      (Fin.append (Fin.append (fun i => componentCarrier B (rB i)) D)
        (fun j => monodromyCarrier.{u} (beta j))) A) :
    SurgeryTopologyConclusion A B := by
  classical
  let kindD : Fin n → SurgerySummandKind := fun i =>
    if Nonempty (SurgerySphereBundle (D i)) then .sphereBundle else .spaceform
  let kind : Fin ((m + n) + k) → SurgerySummandKind :=
    Fin.append (Fin.append (fun _ => .survivor) kindD) (fun _ => .sphereBundle)
  have hnon (i : Fin n) : kindD i ≠ .survivor := by
    dsimp only [kindD]
    split <;> decide
  have hsurvivor : ∀ i, kind i = .survivor →
      ∃ j : Fin m, i = Fin.castAdd k (Fin.castAdd n j) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j _
        exact ⟨j, rfl⟩
      · intro j hj
        exact (hnon j (by simpa only [kind, Fin.append_left, Fin.append_right] using hj)).elim
    · intro j hj
      simp only [kind, Fin.append_right] at hj
      cases hj
  refine {
    piece_count := (m + n) + k
    piece := Fin.append (Fin.append (fun i => componentCarrier B (rB i)) D)
      (fun j => monodromyCarrier.{u} (beta j))
    piece_compact := ?_
    piece_connected := ?_
    kind := kind
    survivor_region := Fin.append (Fin.append UB.region (fun _ => ∅)) (fun _ => ∅)
    survivor := ?_
    survivor_component := ?_
    survivor_cover := ?_
    survivor_disjoint := ?_
    bundles := ?_
    spaceforms := ?_
    reconstruction := S }
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        rw [Fin.append_left, Fin.append_left]
        exact componentCarrier_compact B hB (rB j)
      · intro j
        rw [Fin.append_left, Fin.append_right]
        exact hDcompact j
    · intro j
      rw [Fin.append_right]
      exact monodromyCarrier_compact (beta j)
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        rw [Fin.append_left, Fin.append_left]
        exact componentCarrier_connected B (rB j)
      · intro j
        rw [Fin.append_left, Fin.append_right]
        exact hDconnected j
    · intro j
      rw [Fin.append_right]
      exact monodromyCarrier_connected (beta j)
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j _
        rw [Fin.append_left, Fin.append_left, Fin.append_left, Fin.append_left]
        exact UB.identify j
      · intro j hj
        exact (hnon j (by simpa only [kind, Fin.append_left, Fin.append_right] using hj)).elim
    · intro j hj
      simp only [kind, Fin.append_right] at hj
      cases hj
  · intro i hi
    obtain ⟨j, rfl⟩ := hsurvivor i hi
    exact ⟨rB j, by simpa only [Fin.append_left] using hregionB j⟩
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, UB.region i := UB.cover.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨Fin.castAdd k (Fin.castAdd n i), by simp only [kind, Fin.append_left]⟩, ?_⟩
    simpa only [Fin.append_left] using hi
  · intro i j hij hi hj
    obtain ⟨i', rfl⟩ := hsurvivor i hi
    obtain ⟨j', rfl⟩ := hsurvivor j hj
    simpa only [Fin.append_left] using UB.pairwise_disjoint i' j'
      (fun h => hij (congrArg (fun l => Fin.castAdd k (Fin.castAdd n l)) h))
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j hj
        simp only [kind, Fin.append_left] at hj
        cases hj
      · intro j hj
        simp only [kind, Fin.append_left, Fin.append_right] at hj ⊢
        by_cases hb : Nonempty (SurgerySphereBundle (D j))
        · exact hb
        · simp [kindD, hb] at hj
    · intro j _
      simpa only [Fin.append_right] using
        (⟨monodromySphereBundle (beta j)⟩ : Nonempty (SurgerySphereBundle
          (monodromyCarrier.{u} (beta j))))
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j hj
        simp only [kind, Fin.append_left] at hj
        cases hj
      · intro j hj
        simp only [kind, Fin.append_left, Fin.append_right] at hj ⊢
        have hb : ¬ Nonempty (SurgerySphereBundle (D j)) := by
          intro hb
          simp [kindD, hb] at hj
        exact (hDstandard j).resolve_left hb
    · intro j hj
      simp only [kind, Fin.append_right] at hj
      cases hj






noncomputable def eventAssemblyWitness
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    {m n k : ℕ} (rB : Fin m → (F.slice T).carrier)
    (UB : SmoothDisjointUnionData (fun i => componentCarrier (F.slice T) (rB i))
      (F.slice T))
    (hregionB : ∀ i, UB.region i = connectedComponent (rB i))
    (rD : Fin n → (cappedDiscardedCarrier F T hT P).carrier)
    (hstandard : ∀ x : (cappedDiscardedCarrier F T hT P).carrier,
      Nonempty (SurgerySphereBundle
        (componentCarrier (cappedDiscardedCarrier F T hT P) x)) ∨
      Nonempty (SurgeryPositiveSpaceform
        (componentCarrier (cappedDiscardedCarrier F T hT P) x)))
    (beta : Fin k → Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (S : SmoothFiniteConnectedSumAssembly
      (Fin.append
        (Fin.append (fun i => componentCarrier (F.slice T) (rB i))
          (fun i => componentCarrier (cappedDiscardedCarrier F T hT P) (rD i)))
        (fun j => monodromyCarrier.{u} (beta j)))
      (F.slice (F.event T hT).tMinus)) : RawNonemptyTopologyWitness F T hT :=
  nonemptyWitness F T hT (eventAssemblyConclusion rB UB hregionB
    (F.slices_compact T (F.surgery_times_subset hT))
    (fun i => componentCarrier (cappedDiscardedCarrier F T hT P) (rD i))
    (fun i => componentCarrier_compact _ (cappedDiscardedCarrier_compact F T hT P) (rD i))
    (fun i => componentCarrier_connected _ (rD i))
    (fun i => hstandard (rD i)) beta S)

end PoincareConjecture.M38
