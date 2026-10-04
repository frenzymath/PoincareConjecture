import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.StandardHierarchySurfaces

/-!
# The first complete cuts of the original target handles

The closed period maps use the original quotient representatives and
retain both whole new faces, their exact paired fibers and every old
boundary point. See Waldhausen1968, pp.57--60, and rigidity050,
sections1,3--4. These are target cuts, not cuts of source preimages.
-/

set_option autoImplicit false

open Set Metric Topology

namespace PoincareMT.M76

local notation "D1" => closedBall (0 : Fin 1 → ℝ) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "H1" => LatticeHandle (Fin 1) (Fin 2) L1
local notation "p0" => (4 * (16 : ℝ))
local notation "p1" => (4 * (128 : ℝ))
local notation "C0" => AddCircle p0
local notation "C1" => AddCircle p1

/-- The total original quotient projection of the first closed
three-torus cut. Its closed source is retained below. See050. -/
noncomputable def hamiltonZeroHierarchyCut : C((C0 × C0) × ℝ, H0) :=
  ⟨fun z => hamiltonZeroHierarchyCoordinates.symm (AddCircle.productCutMap p0 z),
    hamiltonZeroHierarchyCoordinates.symm.continuous.comp
      (AddCircle.productCutMap p0).continuous⟩

/-- The complete cut uses the literal three original quotient
coordinates, with no change of lattice or translate. See050. -/
theorem hamiltonZeroHierarchyCut_coe (s t u : ℝ) :
    hamiltonZeroHierarchyCut (((s : C0), (t : C0)), u) =
      (⟨0, mem_closedBall_self zero_le_one⟩, QuotientAddGroup.mk ![s, t, u]) :=
  hamiltonZeroHierarchyCoordinates_symm_coe s t u

/-- The whole closed first cut covers the original closed handle.
See rigidity050, sections1,3. -/
theorem hamiltonZeroHierarchyCut_image :
    hamiltonZeroHierarchyCut '' ((univ : Set (C0 × C0)) ×ˢ Icc 0 p0) = univ := by
  let : Fact (0 < p0) := ⟨by norm_num⟩
  change (hamiltonZeroHierarchyCoordinates.symm ∘ AddCircle.productCutMap p0) '' _ = _
  rw [image_comp, AddCircle.productCutMap_image, image_univ]
  exact hamiltonZeroHierarchyCoordinates.symm.surjective.range_eq

/-- Both complete new torus faces have the same original marked
parametrization. See Waldhausen p.57 and rigidity050. -/
theorem hamiltonZeroHierarchyCut_endpoints (z : C0 × C0) :
    hamiltonZeroHierarchyCut (z, 0) = hamiltonZeroHierarchyTorus z ∧
      hamiltonZeroHierarchyCut (z, p0) = hamiltonZeroHierarchyTorus z :=
  ⟨congrArg hamiltonZeroHierarchyCoordinates.symm
      (AddCircle.productCutMap_endpoints p0 z).1,
    congrArg hamiltonZeroHierarchyCoordinates.symm
      (AddCircle.productCutMap_endpoints p0 z).2⟩

/-- In the complete closed first cut, only corresponding end-face
points are identified. See rigidity050, sections1,3. -/
theorem hamiltonZeroHierarchyCut_eq_iff {z w : (C0 × C0) × ℝ}
    (hz : z.2 ∈ Icc 0 p0) (hw : w.2 ∈ Icc 0 p0) :
    hamiltonZeroHierarchyCut z = hamiltonZeroHierarchyCut w ↔
      z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p0) ∨
        (z.2 = p0 ∧ w.2 = 0)) := by
  let : Fact (0 < p0) := ⟨by norm_num⟩
  change hamiltonZeroHierarchyCoordinates.symm (AddCircle.productCutMap p0 z) =
    hamiltonZeroHierarchyCoordinates.symm (AddCircle.productCutMap p0 w) ↔ _
  rw [hamiltonZeroHierarchyCoordinates.symm.injective.eq_iff]
  exact AddCircle.productCutMap_eq_iff p0 hz hw

/-- The preimage of the entire target torus in the closed cut
consists precisely of its two full end faces. See050. -/
theorem hamiltonZeroHierarchyCut_mem_torus {z : (C0 × C0) × ℝ}
    (hz : z.2 ∈ Icc 0 p0) :
    hamiltonZeroHierarchyCut z ∈ range hamiltonZeroHierarchyTorus ↔
      z.2 = 0 ∨ z.2 = p0 := by
  let : Fact (0 < p0) := ⟨by norm_num⟩
  rw [range_hamiltonZeroHierarchyTorus]
  change (hamiltonZeroHierarchyCoordinates (hamiltonZeroHierarchyCoordinates.symm
    (AddCircle.productCutMap p0 z))).2 = 0 ↔ _
  rw [hamiltonZeroHierarchyCoordinates.apply_symm_apply]
  exact AddCircle.coe_eq_zero_iff_endpoints hz

/-- The first closed torus cut has no old-boundary points.
See rigidity050, section3. -/
theorem hamiltonZeroHierarchyCut_preimage_boundary :
    hamiltonZeroHierarchyCut ⁻¹' latticeHandleBoundary (Fin 0) (Fin 3) L0 = ∅ := by
  rw [hamiltonZeroHandleBoundary_eq_empty, preimage_empty]

/-- The actual compact closed cut gives the original handle its
quotient topology, with the paired fibers proved above. See050. -/
theorem isQuotientMap_hamiltonZeroHierarchyCut :
    IsQuotientMap (fun z : (C0 × C0) × Icc (0 : ℝ) p0 =>
      hamiltonZeroHierarchyCut (z.1, (z.2 : ℝ))) := by
  let : Fact (0 < p0) := ⟨by norm_num⟩
  exact hamiltonZeroHierarchyCoordinates.symm.isQuotientMap.comp
    (AddCircle.isQuotientMap_productCut p0)

/-- The total original quotient projection of the first annulus
cut retains the complete original interval coordinate. See050. -/
noncomputable def hamiltonOneHierarchyCut : C((D1 × C1) × ℝ, H1) :=
  ⟨fun z => hamiltonOneHierarchyCoordinates.symm (AddCircle.productCutMap p1 z),
    hamiltonOneHierarchyCoordinates.symm.continuous.comp
      (AddCircle.productCutMap p1).continuous⟩

/-- The first annulus cut retains the literal original interval
point and both original quotient coordinates. See050, section4. -/
theorem hamiltonOneHierarchyCut_coe (x : D1) (s t : ℝ) :
    hamiltonOneHierarchyCut ((x, (s : C1)), t) =
      (x, QuotientAddGroup.mk ![s, t]) :=
  hamiltonOneHierarchyCoordinates_symm_coe x s t

/-- The complete closed annulus cut covers the entire original
interval-torus handle. See rigidity050, sections1,4. -/
theorem hamiltonOneHierarchyCut_image :
    hamiltonOneHierarchyCut '' ((univ : Set (D1 × C1)) ×ˢ Icc 0 p1) = univ := by
  let : Fact (0 < p1) := ⟨by norm_num⟩
  change (hamiltonOneHierarchyCoordinates.symm ∘ AddCircle.productCutMap p1) '' _ = _
  rw [image_comp, AddCircle.productCutMap_image, image_univ]
  exact hamiltonOneHierarchyCoordinates.symm.surjective.range_eq

/-- Both whole annulus faces retain the same original surface,
including every point of both rim circles. See050. -/
theorem hamiltonOneHierarchyCut_endpoints (z : D1 × C1) :
    hamiltonOneHierarchyCut (z, 0) = hamiltonOneHierarchyAnnulus z ∧
      hamiltonOneHierarchyCut (z, p1) = hamiltonOneHierarchyAnnulus z :=
  ⟨congrArg hamiltonOneHierarchyCoordinates.symm
      (AddCircle.productCutMap_endpoints p1 z).1,
    congrArg hamiltonOneHierarchyCoordinates.symm
      (AddCircle.productCutMap_endpoints p1 z).2⟩

/-- All fibers of the complete closed annulus cut are exactly
the matching end-face pairs or singleton points. See050. -/
theorem hamiltonOneHierarchyCut_eq_iff {z w : (D1 × C1) × ℝ}
    (hz : z.2 ∈ Icc 0 p1) (hw : w.2 ∈ Icc 0 p1) :
    hamiltonOneHierarchyCut z = hamiltonOneHierarchyCut w ↔
      z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p1) ∨
        (z.2 = p1 ∧ w.2 = 0)) := by
  let : Fact (0 < p1) := ⟨by norm_num⟩
  change hamiltonOneHierarchyCoordinates.symm (AddCircle.productCutMap p1 z) =
    hamiltonOneHierarchyCoordinates.symm (AddCircle.productCutMap p1 w) ↔ _
  rw [hamiltonOneHierarchyCoordinates.symm.injective.eq_iff]
  exact AddCircle.productCutMap_eq_iff p1 hz hw

/-- Exactly the two complete transverse annulus faces map to the
original annulus inside the closed cut. See050, sections1,4. -/
theorem hamiltonOneHierarchyCut_mem_annulus {z : (D1 × C1) × ℝ}
    (hz : z.2 ∈ Icc 0 p1) :
    hamiltonOneHierarchyCut z ∈ range hamiltonOneHierarchyAnnulus ↔
      z.2 = 0 ∨ z.2 = p1 := by
  let : Fact (0 < p1) := ⟨by norm_num⟩
  rw [range_hamiltonOneHierarchyAnnulus]
  change (hamiltonOneHierarchyCoordinates (hamiltonOneHierarchyCoordinates.symm
    (AddCircle.productCutMap p1 z))).2 = 0 ↔ _
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
  exact AddCircle.coe_eq_zero_iff_endpoints hz

/-- The full old boundary pulls back to every original annulus
rim fiber for all real times, hence also on the complete cut. See050. -/
theorem hamiltonOneHierarchyCut_preimage_boundary :
    hamiltonOneHierarchyCut ⁻¹' latticeHandleBoundary (Fin 1) (Fin 2) L1 =
      hamiltonOneAnnulusRim ×ˢ univ := by
  rw [← hamiltonOneHierarchyCoordinates_preimage_boundary]
  ext z
  change hamiltonOneHierarchyCoordinates (hamiltonOneHierarchyCoordinates.symm
    (AddCircle.productCutMap p1 z)) ∈ hamiltonOneAnnulusRim ×ˢ univ ↔ _
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
  rfl

/-- The actual compact annulus cut supplies the original quotient
topology on the entire interval-torus handle. See050. -/
theorem isQuotientMap_hamiltonOneHierarchyCut :
    IsQuotientMap (fun z : (D1 × C1) × Icc (0 : ℝ) p1 =>
      hamiltonOneHierarchyCut (z.1, (z.2 : ℝ))) := by
  let : Fact (0 < p1) := ⟨by norm_num⟩
  exact hamiltonOneHierarchyCoordinates.symm.isQuotientMap.comp
    (AddCircle.isQuotientMap_productCut p1)

end PoincareMT.M76
