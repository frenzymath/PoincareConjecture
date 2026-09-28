import PoincareConjecture.Proofs.M02.Topology.IntegralOpenCapProperty
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapTwoCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportCapThreeCanonicalUnion
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportEmpty
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportHomeomorph

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits TopologicalSpace Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

open PoincareConjecture.Proofs.M02

variable {X : Type} [TopologicalSpace X] [T2Space X] [RegularSpace X]
  [LocallyCompactSpace X]
  (hDX : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
  (omegaX : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
  (hlocalX : ∀ x : X, ∃ B : Set X, IsOpen B ∧ x ∈ B ∧
    ∃ c : integralSupportHomology B 3, ∀ y : X, ∀ hy : y ∈ B,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 c = omegaX y)

theorem integralOpenCapProperty_empty :
    integralOpenCapProperty hDX omegaX hlocalX (∅ : Set X) isOpen_empty := by
  let : LocallyCompactSpace (∅ : Set X) := isOpen_empty.locallyCompactSpace
  let e : (∅ : Set X) ≃ₜ (∅ : Set (EuclideanSpace Real (Fin 3))) :=
    { toEquiv := Equiv.equivOfIsEmpty _ _
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  have hc (q : Nat) : IsZero (integralCompactSupportCohomology (∅ : Set X) q) := by
    let := integralCompactSupportCohomologyOpenMap_homeomorph_isIso e q
    exact (integralCompactSupportCohomology_empty_isZero q).of_iso
      (asIso (integralCompactSupportCohomologyOpenMap
        (e : C((∅ : Set X), (∅ : Set (EuclideanSpace Real (Fin 3)))))
        e.isOpenEmbedding q))
  dsimp [integralOpenCapProperty]
  refine ⟨?_, ?_, ?_, fun q _ => hc q⟩
  · exact (integralHomology_empty_isZero (X := X) 2).epi _
  · exact (hc 2).isIso
      (integralHomology_empty_isZero (X := X) 1) _
  · exact (hc 3).isIso
      (integralHomology_empty_isZero (X := X) 0) _

theorem integralOpenCapProperty_union
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hPU : integralOpenCapProperty hDX omegaX hlocalX U hU)
    (hPV : integralOpenCapProperty hDX omegaX hlocalX V hV)
    (hPI : integralOpenCapProperty hDX omegaX hlocalX (U ∩ V) (hU.inter hV)) :
    integralOpenCapProperty hDX omegaX hlocalX (U ∪ V) (hU.union hV) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let : LocallyCompactSpace (↥(U ∩ V)) := (hU.inter hV).locallyCompactSpace
  let : LocallyCompactSpace (↥(U ∪ V)) := (hU.union hV).locallyCompactSpace
  dsimp [integralOpenCapProperty] at hPU hPV hPI ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact integralCompactSupportCapOne_union_epi_canonical U V hU hV
      hDX omegaX hlocalX hPU.1 hPV.1 hPU.2.1 hPV.2.1 hPI.2.1
  · exact integralCompactSupportCapTwo_union_isIso_canonical U V hU hV
      hDX omegaX hlocalX hPU.2.1 hPV.2.1 hPI.2.1
      hPU.2.2.1 hPV.2.2.1 hPI.2.2.1
  · exact integralCompactSupportCapThree_union_isIso_canonical U V hU hV
      hDX omegaX hlocalX hPU.2.2.1 hPV.2.2.1 hPI.2.2.1 (hPI.2.2.2 4 le_rfl)
  · intro q hq
    have hpair : IsZero
        (integralCompactSupportCohomology U q ⊞ integralCompactSupportCohomology V q) :=
      (biprod_isZero_iff _ _).mpr ⟨hPU.2.2.2 q hq, hPV.2.2.2 q hq⟩
    exact (integralCompactSupportOpenMayerVietoris_exact_union U V hU hV q).isZero_of_both_isZero
      hpair (hPI.2.2.2 (q + 1) (by omega))

end PoincareConjecture.Proofs.M02.Topology
