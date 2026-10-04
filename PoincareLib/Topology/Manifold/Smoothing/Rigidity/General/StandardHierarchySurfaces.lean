import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.StandardHierarchyCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.Mathlib.ProductCircleCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.Mathlib.RetractionFundamentalGroup

/-!
# The actual first target torus and annulus

The original fixed lattice coordinates give complete compact embedded
surfaces and literal retractions. Their full old-boundary preimages and
based group injections retain the original handles. See Waldhausen1968,
pp.57--60, and rigidity050, sections3--4. Source preimage surfaces and
the subsequent hierarchy are not asserted here.
-/

set_option autoImplicit false

open Set Metric Topology

namespace PoincareMT.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "H1" => LatticeHandle (Fin 1) (Fin 2) L1
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "C1" => AddCircle (4 * (128 : ℝ))

/-- The whole first torus in the original closed handle. Its last
circle coordinate is the original zero class. See rigidity050. -/
noncomputable def hamiltonZeroHierarchyTorus : C(C0 × C0, H0) :=
  ⟨fun z => hamiltonZeroHierarchyCoordinates.symm (z, 0),
    hamiltonZeroHierarchyCoordinates.symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩

/-- The literal two-circle projection retracts the original handle
onto its first target torus. See rigidity050, section3. -/
noncomputable def hamiltonZeroHierarchyRetraction : C(H0, C0 × C0) :=
  ⟨fun x => (hamiltonZeroHierarchyCoordinates x).1,
    continuous_fst.comp hamiltonZeroHierarchyCoordinates.continuous⟩

/-- Retraction recovers every original torus point exactly.
See rigidity050, sections2--3. -/
theorem hamiltonZeroHierarchyRetraction_leftInverse :
    Function.LeftInverse hamiltonZeroHierarchyRetraction hamiltonZeroHierarchyTorus := by
  intro z
  change (hamiltonZeroHierarchyCoordinates
    (hamiltonZeroHierarchyCoordinates.symm (z, 0))).1 = z
  rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply]

/-- The actual torus has the complete zero-coordinate fiber as its
image, including every original period identification. See050. -/
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

/-- The entire first torus is embedded in the original handle.
See Waldhausen pp.57--60 and rigidity050, section3. -/
theorem isEmbedding_hamiltonZeroHierarchyTorus :
    IsEmbedding hamiltonZeroHierarchyTorus :=
  hamiltonZeroHierarchyCoordinates.symm.isEmbedding.comp
    (AddCircle.isEmbedding_productSection (4 * (16 : ℝ)))

/-- Compactness applies to the whole original target torus.
See rigidity050, section3. -/
theorem isCompact_range_hamiltonZeroHierarchyTorus :
    IsCompact (range hamiltonZeroHierarchyTorus) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  rw [← image_univ]
  exact isCompact_univ.image hamiltonZeroHierarchyTorus.continuous

/-- The original closed handle has no old boundary on the first
torus. See rigidity050, section3. -/
theorem hamiltonZeroHierarchyTorus_preimage_boundary :
    hamiltonZeroHierarchyTorus ⁻¹' latticeHandleBoundary (Fin 0) (Fin 3) L0 = ∅ := by
  rw [hamiltonZeroHandleBoundary_eq_empty, preimage_empty]

/-- The actual torus inclusion is injective on based fundamental
groups at every point by its literal retraction. See050, section2. -/
theorem hamiltonZeroHierarchyTorus_pi1_injective (z : C0 × C0) :
    Function.Injective (FundamentalGroup.map hamiltonZeroHierarchyTorus z) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    hamiltonZeroHierarchyRetraction_leftInverse z

/-- The whole first annulus retains the original closed interval
coordinate and the first original circle. See rigidity050, section4. -/
noncomputable def hamiltonOneHierarchyAnnulus : C(D1 × C1, H1) :=
  ⟨fun z => hamiltonOneHierarchyCoordinates.symm (z, 0),
    hamiltonOneHierarchyCoordinates.symm.continuous.comp
      (continuous_id.prodMk continuous_const)⟩

/-- The actual original-coordinate projection onto the whole
target annulus. See rigidity050, section4. -/
noncomputable def hamiltonOneHierarchyRetraction : C(H1, D1 × C1) :=
  ⟨fun x => (hamiltonOneHierarchyCoordinates x).1,
    continuous_fst.comp hamiltonOneHierarchyCoordinates.continuous⟩

/-- Retraction fixes every original annulus point, including its
whole rim. See rigidity050, sections2--4. -/
theorem hamiltonOneHierarchyRetraction_leftInverse :
    Function.LeftInverse hamiltonOneHierarchyRetraction hamiltonOneHierarchyAnnulus := by
  intro z
  change (hamiltonOneHierarchyCoordinates
    (hamiltonOneHierarchyCoordinates.symm (z, 0))).1 = z
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]

/-- The complete image of the first annulus is its literal zero
last-coordinate fiber in the original handle. See050, section4. -/
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

/-- The first annulus, including both rim circles, is embedded in
the actual original handle. See rigidity050, section4. -/
theorem isEmbedding_hamiltonOneHierarchyAnnulus :
    IsEmbedding hamiltonOneHierarchyAnnulus :=
  hamiltonOneHierarchyCoordinates.symm.isEmbedding.comp
    (AddCircle.isEmbedding_productSection (4 * (128 : ℝ)))

/-- The complete first target annulus is compact.
See rigidity050, section4. -/
theorem isCompact_range_hamiltonOneHierarchyAnnulus :
    IsCompact (range hamiltonOneHierarchyAnnulus) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  rw [← image_univ]
  exact isCompact_univ.image hamiltonOneHierarchyAnnulus.continuous

/-- The entire old-boundary preimage is the original annulus rim.
Both norm-one interval endpoints retain every circle point. See050. -/
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

/-- The original annulus inclusion is injective on based groups
at every point by its actual retraction. See rigidity050, section2. -/
theorem hamiltonOneHierarchyAnnulus_pi1_injective (z : D1 × C1) :
    Function.Injective (FundamentalGroup.map hamiltonOneHierarchyAnnulus z) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    hamiltonOneHierarchyRetraction_leftInverse z

end PoincareMT.M76
