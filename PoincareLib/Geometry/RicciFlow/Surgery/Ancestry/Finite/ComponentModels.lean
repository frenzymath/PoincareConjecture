import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Theory
import PoincareLib.Geometry.Spacetime.Realization.Manifold.OpenSubsetDiffeomorph

/-!
# M56 selected-component models

This file supplies the local open-submanifold model for a connected component
of a compact smooth slice. The construction is the component model used in
Morgan--Tian Definition 18.2 and Proposition 15.3 (printed pp. 357--358,
419--420). Its inverse is only required to be smooth on the displayed range,
as required by `SurgerySelectedComponent`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The open-submanifold carrier used for MT Definition 18.2, pp. 419--420. -/
noncomputable def m56OpenCarrier (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) : GeneralizedSliceCarrier.{u} where
  carrier := U
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

private theorem m56Component_range
    {A : GeneralizedSliceCarrier.{u}} (x : A.carrier)
    (U : TopologicalSpace.Opens A.carrier)
    (hopen : IsOpen (connectedComponent x))
    (hU : U = ⟨connectedComponent x, hopen⟩) :
    Set.range (fun y : (m56OpenCarrier A U).carrier => y.1) =
      connectedComponent x := by
  change Set.range (fun y : U => (y : A.carrier)) = connectedComponent x
  subst hU
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

private noncomputable def m56ComponentInverse
    {A : GeneralizedSliceCarrier.{u}} (x : A.carrier)
    (U : TopologicalSpace.Opens A.carrier)
    (hU : U = ⟨connectedComponent x, by
      let : LocallyConnectedSpace A.carrier :=
        ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) A.carrier
      exact isOpen_connectedComponent⟩) :
    A.carrier → U := by
  classical
  exact fun y => if hy : y ∈ U then ⟨y, hy⟩ else ⟨x, by
    rw [hU]
    exact mem_connectedComponent⟩

private theorem m56Component_inverse_smooth
    {A : GeneralizedSliceCarrier.{u}} (x : A.carrier)
    (U : TopologicalSpace.Opens A.carrier)
    (hopen : IsOpen (connectedComponent x))
    (hU : U = ⟨connectedComponent x, hopen⟩) :
    let C := m56OpenCarrier A U
    let inclusion : C.carrier → A.carrier := fun y => y.1
    let inverse : A.carrier → C.carrier := m56ComponentInverse x U hU
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse (Set.range inclusion) := by
  classical
  let inverse' : A.carrier → U := m56ComponentInverse x U hU
  change ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse'
    (Set.range (fun z : U => (z : A.carrier)))
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  have hval : ∀ q ∈ Set.range (fun z : U => (z : A.carrier)),
      (Subtype.val ∘ inverse') q = q := by
    intro q hq
    obtain ⟨q', rfl⟩ := hq
    change (m56ComponentInverse x U hU (q' : A.carrier) : A.carrier) = q'
    simp [m56ComponentInverse, q'.property]
  rw [← ContMDiffWithinAt.subtypeVal_comp_iff U inverse'
    (Set.range (fun z : U => (z : A.carrier))) (z : A.carrier)]
  exact (contMDiffWithinAt_congr hval (hval _ ⟨z, rfl⟩)).mpr
    contMDiffWithinAt_id

/-- The connected component model for MT Definition 18.2, pp. 419--420. -/
noncomputable def m56SelectedComponent
    {A : GeneralizedSliceCarrier.{u}} (hcompact : IsCompact (Set.univ : Set A.carrier))
    (x : A.carrier) : SurgerySelectedComponent A := by
  classical
  let : LocallyConnectedSpace A.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) A.carrier
  let hopen : IsOpen (connectedComponent x) := isOpen_connectedComponent
  let U : TopologicalSpace.Opens A.carrier :=
    ⟨connectedComponent x, hopen⟩
  let C := m56OpenCarrier A U
  let inclusion : C.carrier → A.carrier := fun y => y.1
  let inverse : A.carrier → C.carrier := fun y =>
    if hy : y ∈ U then ⟨y, hy⟩ else ⟨x, by
      change x ∈ connectedComponent x
      exact mem_connectedComponent⟩
  refine {
    carrier := C
    basepoint := ⟨x, mem_connectedComponent⟩
    inclusion := inclusion
    inverse := inverse
    inclusion_openEmbedding := U.2.isOpenEmbedding_subtypeVal
    inclusion_smooth := contMDiff_subtype_val
    inverse_smooth := ?_
    left_inverse := ?_
    range_eq_component := ?_
    compact := ?_
    connected := ?_ }
  · exact m56Component_inverse_smooth x U hopen rfl
  · intro y
    apply Subtype.ext
    simp [inverse, inclusion, y.property]
  · exact m56Component_range x U hopen rfl
  · change IsCompact (Set.univ : Set U)
    rw [Subtype.isCompact_iff]
    simpa [U] using (hcompact.of_isClosed_subset
      (isClosed_connectedComponent (x := x)) (subset_univ _))
  · change IsConnected (Set.univ : Set U)
    let : ConnectedSpace U := Subtype.connectedSpace
      (isConnected_connectedComponent (x := x))
    exact isConnected_univ

/-- The selected model has the actual point's component as its range
(MT Definition 18.2, pp. 419--420). -/
theorem m56SelectedComponent_range {A : GeneralizedSliceCarrier.{u}}
    (hcompact : IsCompact (Set.univ : Set A.carrier)) (x : A.carrier) :
    Set.range (m56SelectedComponent hcompact x).inclusion = connectedComponent x :=
  (m56SelectedComponent hcompact x).range_eq_component

end PoincareMT
