import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Topology.Connected.LocallyConnected









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38


noncomputable def openCarrier (S : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens S.carrier) : GeneralizedSliceCarrier.{u} where
  carrier := U
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance



noncomputable def openRegionEquivalence (S : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens S.carrier) (x : U) :
    SurgeryRegionEquivalence (openCarrier S U) S Set.univ U := by
  classical
  let inverse : S.carrier → U := fun y => if hy : y ∈ U then ⟨y, hy⟩ else x
  have hinverse (y : S.carrier) (hy : y ∈ U) : (inverse y).1 = y := by
    simp [inverse, hy]
  refine
    { map := Subtype.val
      inverse := inverse
      map_image := ?_
      inverse_image := ?_
      left_inverse := ?_
      right_inverse := hinverse
      map_smooth := contMDiff_subtype_val.contMDiffOn
      inverse_smooth := ?_ }
  · apply Set.Subset.antisymm
    · rintro y ⟨z, _, rfl⟩
      exact z.property
    · intro y hy
      exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
  · apply Set.eq_univ_of_forall
    intro y
    refine ⟨y.1, y.2, ?_⟩
    apply Subtype.ext
    exact hinverse y.1 y.2
  · intro y _
    apply Subtype.ext
    exact hinverse y.1 y.2
  · intro y hy
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U inverse U y).mp
    have h : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ inverse) U :=
      contMDiffOn_id.congr (fun z hz => hinverse z hz)
    exact h y hy


def componentOpen (S : GeneralizedSliceCarrier.{u}) (x : S.carrier) :
    TopologicalSpace.Opens S.carrier := by
  let : LocallyConnectedSpace S.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) S.carrier
  exact ⟨connectedComponent x, isOpen_connectedComponent⟩


noncomputable def componentCarrier (S : GeneralizedSliceCarrier.{u}) (x : S.carrier) :
    GeneralizedSliceCarrier.{u} :=
  openCarrier S (componentOpen S x)


noncomputable def componentRegionEquivalence (S : GeneralizedSliceCarrier.{u})
    (x : S.carrier) :
    SurgeryRegionEquivalence (componentCarrier S x) S Set.univ (connectedComponent x) :=
  openRegionEquivalence S (componentOpen S x) ⟨x, mem_connectedComponent⟩


theorem componentCarrier_connected (S : GeneralizedSliceCarrier.{u}) (x : S.carrier) :
    IsConnected (Set.univ : Set (componentCarrier S x).carrier) := by
  change IsConnected (Set.univ : Set (connectedComponent x))
  let : ConnectedSpace (connectedComponent x) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  exact isConnected_univ


theorem componentCarrier_compact (S : GeneralizedSliceCarrier.{u})
    (hS : IsCompact (Set.univ : Set S.carrier)) (x : S.carrier) :
    IsCompact (Set.univ : Set (componentCarrier S x).carrier) := by
  change IsCompact (Set.univ : Set (connectedComponent x))
  let : CompactSpace S.carrier := isCompact_univ_iff.mp hS
  let : CompactSpace (connectedComponent x) :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  exact isCompact_univ



theorem finite_components (S : GeneralizedSliceCarrier.{u})
    (hS : IsCompact (Set.univ : Set S.carrier)) :
    Finite (ConnectedComponents S.carrier) := by
  let : LocallyConnectedSpace S.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) S.carrier
  let : CompactSpace S.carrier := isCompact_univ_iff.mp hS
  infer_instance

end PoincareConjecture.M38
