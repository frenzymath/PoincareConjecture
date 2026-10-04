import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.MeridianCutFrontierPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.MeridianCutFrontierInjective
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.MeridianCutFrontierImage

/-!
# The full cut frontier with its literal parameter map

Compactness and the actual injection give a homeomorphism onto the
entire physical-cut frontier, including all cap rims. See042, section3.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "T" => (Fin 1 → ℝ) ⧸ Submodule.toAddSubgroup (hamiltonLowerPeriodLattice (Fin 1))
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}

/-- The complete parameter sphere is homeomorphic to the whole
cut frontier by the same total cap-cylinder map. See042, section3. -/
theorem exists_meridianCutFrontier_homeomorph (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a : ℝ} (ha : 0 < a) (hasmall : a ≤ 1 / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hC : PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap
      (Q ×ˢ Icc (a / 2) (p - a / 2))) :
    ∃ h : cubePrismBoundary (a / 2) (p - a / 2) ≃ₜ frontier P.cutCarrier,
      ∀ z, (h z : X) = P.meridianCutFrontierMap a z := by
  let : T2Space T := hamiltonSolidTorusCircleEquiv.isEmbedding.t2Space
  have hgap : a / 2 < p - a / 2 := by norm_num at hasmall ⊢; linarith
  let S : Set E := cubePrismBoundary (a / 2) (p - a / 2)
  let f : E → X := P.meridianCutFrontierMap a
  obtain ⟨K, hK, hKS⟩ := exists_finite_cubePrismBoundary hgap
  have hS : IsCompact S := by
    change IsCompact (cubePrismBoundary (a / 2) (p - a / 2))
    rw [← hKS]
    exact K.isCompact_space_of_finite hK
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hPL := P.polyhedral_meridianCutFrontierMap he hgap hmark hC
  have hc : Continuous (fun z : S => f z) :=
    continuousOn_iff_continuous_domRestrict.mp hPL.continuousOn
  let H : S ≃ₜ f '' S := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn f S (P.injective_meridianCutFrontierMap ha hgap hmark))
    (hc.subtype_mk _)
  exact ⟨H.trans (Homeomorph.setCongr
    (P.image_meridianCutFrontierMap_eq_frontier hR hopen ha hasmall hmark)), fun _ => rfl⟩

end PoincareMT.M76.OriginalDiskProduct
