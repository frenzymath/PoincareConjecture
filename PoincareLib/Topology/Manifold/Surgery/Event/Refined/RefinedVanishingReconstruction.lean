import PoincareLib.Topology.Manifold.Surgery.Event.Late.LateReconstruction

/-!
# Vanishing reconstruction with refined standard summands

Retain a supplied classified-piece assembly literally and use only bundle
and spaceform kinds. The actual empty post carrier has no survivors. The
event specialization transports this conclusion along its stored late-slice
identification.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- A finite classified-piece assembly gives the no-survivor conclusion
of Morgan--Tian Proposition 15.3, pp. 357-358. The exact piece family and
assembly are preserved; no component classification is inferred here. -/
noncomputable def noSurvivorAssemblyConclusion
    {A B : GeneralizedSliceCarrier.{u}} [IsEmpty B.carrier] {n : ℕ}
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (S : SmoothFiniteConnectedSumAssembly D A) : SurgeryTopologyConclusion A B := by
  classical
  let kind : Fin n → SurgerySummandKind := fun i =>
    if Nonempty (SurgerySphereBundle (D i)) then .sphereBundle else .spaceform
  have hnon (i : Fin n) : kind i ≠ .survivor := by
    dsimp only [kind]
    split <;> decide
  exact {
    piece_count := n
    piece := D
    piece_compact := hDcompact
    piece_connected := hDconnected
    kind := kind
    survivor_region := fun _ => ∅
    survivor := fun i hi => (hnon i hi).elim
    survivor_component := fun i hi => (hnon i hi).elim
    survivor_cover := by ext x; exact isEmptyElim x
    survivor_disjoint := fun i _ _ hi _ => (hnon i hi).elim
    bundles := fun i hi => by
      by_cases hb : Nonempty (SurgerySphereBundle (D i))
      · exact hb
      · simp [kind, hb] at hi
    spaceforms := fun i hi => by
      have hb : ¬ Nonempty (SurgerySphereBundle (D i)) := by
        intro hb
        simp [kind, hb] at hi
      exact (hDstandard i).resolve_left hb
    reconstruction := S }

/-- Apply the refined no-survivor construction to the actual selected late
slice and its stored preterminal map. Source: Proposition 15.3, pp. 357-358.
The classified assembly may include several pieces for one late component. -/
noncomputable def vanishingWitnessOfClassifiedAssembly
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier]
    (t : Set.Ico (F.vanishing_event T hT).tMinus T) {n : ℕ}
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (S : SmoothFiniteConnectedSumAssembly D (F.slice t.val)) :
    RawVanishingTopologyWitness F T hT :=
  vanishingWitnessAtLateTime F T hT t
    (noSurvivorAssemblyConclusion D hDcompact hDconnected hDstandard S)

end PoincareMT.M38
