import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ProductCircleCut
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup











set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "H1" => LatticeHandle (Fin 1) (Fin 2) L1
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "C1" => AddCircle (4 * (128 : ℝ))



noncomputable def hamiltonZeroHierarchyTorus : C(C0 × C0, H0) :=
  ⟨fun z => hamiltonZeroHierarchyCoordinates.symm (z, 0),
    hamiltonZeroHierarchyCoordinates.symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩



noncomputable def hamiltonZeroHierarchyRetraction : C(H0, C0 × C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates x).1,
    continuous_fst.comp hamiltonZeroHierarchyCoordinates.continuous⟩



theorem hamiltonZeroHierarchyRetraction_leftInverse :
    Function.LeftInverse hamiltonZeroHierarchyRetraction hamiltonZeroHierarchyTorus := by
  intro z
  change (hamiltonZeroHierarchyCoordinates
    (hamiltonZeroHierarchyCoordinates.symm (z, 0))).1 = z
  rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply]



theorem range_hamiltonZeroHierarchyTorus :
    range hamiltonZeroHierarchyTorus =
      {x | (hamiltonZeroHierarchyCoordinates x).2 = 0} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (hamiltonZeroHierarchyCoordinates
      (hamiltonZeroHierarchyCoordinates.symm (z, 0))).2 = 0
    rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply]
  · intro hx
    refine ⟨(hamiltonZeroHierarchyCoordinates x).1, ?_⟩
    apply hamiltonZeroHierarchyCoordinates.injective
    change hamiltonZeroHierarchyCoordinates (hamiltonZeroHierarchyCoordinates.symm
      ((hamiltonZeroHierarchyCoordinates x).1, 0)) = hamiltonZeroHierarchyCoordinates x
    rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply]
    exact Prod.ext rfl hx.symm



theorem isEmbedding_hamiltonZeroHierarchyTorus :
    IsEmbedding hamiltonZeroHierarchyTorus :=
  hamiltonZeroHierarchyCoordinates.symm.isEmbedding.comp
    (AddCircle.isEmbedding_productSection (4 * (16 : ℝ)))



theorem isCompact_range_hamiltonZeroHierarchyTorus :
    IsCompact (range hamiltonZeroHierarchyTorus) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  rw [← image_univ]
  exact isCompact_univ.image hamiltonZeroHierarchyTorus.continuous



theorem hamiltonZeroHierarchyTorus_preimage_boundary :
    hamiltonZeroHierarchyTorus ⁻¹' latticeHandleBoundary (Fin 0) (Fin 3) L0 = ∅ := by
  rw [hamiltonZeroHandleBoundary_eq_empty, preimage_empty]



theorem hamiltonZeroHierarchyTorus_pi1_injective (z : C0 × C0) :
    Function.Injective (FundamentalGroup.map hamiltonZeroHierarchyTorus z) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    hamiltonZeroHierarchyRetraction_leftInverse z



noncomputable def hamiltonOneHierarchyAnnulus : C(D1 × C1, H1) :=
  ⟨fun z => hamiltonOneHierarchyCoordinates.symm (z, 0),
    hamiltonOneHierarchyCoordinates.symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩



noncomputable def hamiltonOneHierarchyRetraction : C(H1, D1 × C1) :=
  ⟨fun x => (hamiltonOneHierarchyCoordinates x).1,
    continuous_fst.comp hamiltonOneHierarchyCoordinates.continuous⟩



theorem hamiltonOneHierarchyRetraction_leftInverse :
    Function.LeftInverse hamiltonOneHierarchyRetraction hamiltonOneHierarchyAnnulus := by
  intro z
  change (hamiltonOneHierarchyCoordinates
    (hamiltonOneHierarchyCoordinates.symm (z, 0))).1 = z
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]



theorem range_hamiltonOneHierarchyAnnulus :
    range hamiltonOneHierarchyAnnulus =
      {x | (hamiltonOneHierarchyCoordinates x).2 = 0} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change (hamiltonOneHierarchyCoordinates
      (hamiltonOneHierarchyCoordinates.symm (z, 0))).2 = 0
    rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
  · intro hx
    refine ⟨(hamiltonOneHierarchyCoordinates x).1, ?_⟩
    apply hamiltonOneHierarchyCoordinates.injective
    change hamiltonOneHierarchyCoordinates (hamiltonOneHierarchyCoordinates.symm
      ((hamiltonOneHierarchyCoordinates x).1, 0)) = hamiltonOneHierarchyCoordinates x
    rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
    exact Prod.ext rfl hx.symm



theorem isEmbedding_hamiltonOneHierarchyAnnulus :
    IsEmbedding hamiltonOneHierarchyAnnulus :=
  hamiltonOneHierarchyCoordinates.symm.isEmbedding.comp
    (AddCircle.isEmbedding_productSection (4 * (128 : ℝ)))



theorem isCompact_range_hamiltonOneHierarchyAnnulus :
    IsCompact (range hamiltonOneHierarchyAnnulus) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  rw [← image_univ]
  exact isCompact_univ.image hamiltonOneHierarchyAnnulus.continuous



theorem hamiltonOneHierarchyAnnulus_preimage_boundary :
    hamiltonOneHierarchyAnnulus ⁻¹' latticeHandleBoundary (Fin 1) (Fin 2) L1 =
      hamiltonOneAnnulusRim := by
  rw [← hamiltonOneHierarchyCoordinates_preimage_boundary]
  ext z
  change (hamiltonOneHierarchyCoordinates
    (hamiltonOneHierarchyCoordinates.symm (z, 0))) ∈
      hamiltonOneAnnulusRim ×ˢ (univ : Set C1) ↔ z ∈ hamiltonOneAnnulusRim
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
  exact ⟨And.left, fun hz => ⟨hz, mem_univ _⟩⟩



theorem hamiltonOneHierarchyAnnulus_pi1_injective (z : D1 × C1) :
    Function.Injective (FundamentalGroup.map hamiltonOneHierarchyAnnulus z) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    hamiltonOneHierarchyRetraction_leftInverse z

end PoincareConjecture.M76
