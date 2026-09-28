import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.HomologicalAlgebra.ModuleExactDiagram

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace Poincare.Topology

theorem moduleCapD1_union_surjective
    {CUI CUV CU1 CV1 CU2 CV2 : ModuleCat.{u} Int}
    {HU HV HUI HUV HU2 HV2 : ModuleCat.{u} Int}
    (cDelta : CUV ⟶ CUI) (cDiff : CUI ⟶ (CU2 ⊞ CV2))
    (cSum : (CU1 ⊞ CV1) ⟶ CUV)
    (hDelta : HUV ⟶ HUI) (hDiff : HUI ⟶ (HU ⊞ HV))
    (hSum : (HU2 ⊞ HV2) ⟶ HUV)
    (d1U : CU1 ⟶ HU2) (d1V : CV1 ⟶ HV2)
    (d2U : CU2 ⟶ HU) (d2V : CV2 ⟶ HV)
    (d2I : CUI ⟶ HUI) (dUnion : CUV ⟶ HUV)
    (hδd : dUnion ≫ hDelta = cDelta ≫ d2I)
    (hdd : d2I ≫ hDiff = cDiff ≫ biprod.map d2U d2V)
    (hds : cSum ≫ dUnion = biprod.map d1U d1V ≫ hSum)
    (hDeltaDiff : hDelta ≫ hDiff = 0)
    (hExactC : ∀ z : CUI, cDiff z = 0 → ∃ x : CUV, cDelta x = z)
    (hExactH : ∀ y : HUV, hDelta y = 0 → ∃ w, hSum.hom w = y)
    (hD2pair : Function.Injective (biprod.map d2U d2V))
    (hD2I : Function.Surjective d2I)
    (hDU : Function.Surjective d1U) (hDV : Function.Surjective d1V) :
    Function.Surjective dUnion := by
  let : Epi d1U := (ModuleCat.epi_iff_surjective d1U).mpr hDU
  let : Epi d1V := (ModuleCat.epi_iff_surjective d1V).mpr hDV
  exact moduleExactDiagram_surjective cSum cDelta cDiff hSum hDelta hDiff
    (biprod.map d1U d1V) dUnion d2I (biprod.map d2U d2V)
    hds hδd.symm hdd.symm hDeltaDiff hExactC hExactH
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) hD2I hD2pair

end Poincare.Topology
