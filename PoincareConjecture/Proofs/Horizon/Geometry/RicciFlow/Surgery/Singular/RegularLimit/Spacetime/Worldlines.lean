import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.Maps
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.OldBoxes
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.ReferenceCompatibility


set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem regularSpacetimeForward_eq_oldBox_of_eq
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (b : F.box_index) (x : (F.box b).carrier.carrier) (y : H.regularRegion P04)
    {t : ℝ} (ht : t ∈ Ioc H.reference.tMinus T) (hbt : t ∈ (F.box b).interval)
    (heq : H.regularSpacetimeForward P04 (⟨t, ht⟩, y) =
      H.oldSpacetimeForward P04 ⟨t, (F.box b).forward t hbt x⟩)
    {s : ℝ} (hs : s ∈ Ioc H.reference.tMinus T) (hbs : s ∈ (F.box b).interval) :
    H.regularSpacetimeForward P04 (⟨s, hs⟩, y) =
      H.oldSpacetimeForward P04 ⟨s, (F.box b).forward s hbs x⟩ := by
  have htT := (H.interval_preterminal (F.box_interval_subset b hbt)).2
  have hsT := (H.interval_preterminal (F.box_interval_subset b hbs)).2
  rw [H.regularSpacetimeForward_old P04 t ht htT] at heq
  have hbase : H.reference.forward t ⟨ht.1.le, htT⟩ y = (F.box b).forward t hbt x :=
    eq_of_heq (Sigma.mk.inj_iff.mp (H.oldSpacetimeForward_injective P04 heq)).2
  rw [H.regularSpacetimeForward_old P04 s hs hsT]
  apply congrArg (H.oldSpacetimeForward P04)
  apply congrArg (Sigma.mk s)
  exact H.reference.forward_eq_of_eq b x (y : M) ⟨ht.1.le, htT⟩ hbt hbase
    ⟨hs.1.le, hsT⟩ hbs


theorem regularSpacetimeForward_eq_of_eq
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x y : H.regularRegion P04) {t : ℝ} (ht : t ∈ Ioc H.reference.tMinus T)
    (heq : H.regularSpacetimeForward P04 (⟨t, ht⟩, x) =
      H.regularSpacetimeForward P04 (⟨t, ht⟩, y))
    {s : ℝ} (hs : s ∈ Ioc H.reference.tMinus T) :
    H.regularSpacetimeForward P04 (⟨s, hs⟩, x) =
      H.regularSpacetimeForward P04 (⟨s, hs⟩, y) := by
  have hxy := congrArg Prod.snd (H.regularSpacetimeForward_injective P04 heq)
  exact congrArg (fun z => H.regularSpacetimeForward P04 (⟨s, hs⟩, z)) hxy

end PoincareConjecture.SingularTimeAssumptions
