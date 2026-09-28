import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Winding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.OriginalCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourceAnnulusMap

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D1" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C512" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L
local notation "Q" => hamiltonOneHierarchyCoordinates

noncomputable def sourceAnnulusHandleMap (phi : C(H, H)) (theta : C512)
    (A : Ann ≃ₜ sourceSurface phi theta) : C(Ann, H) where
  toFun z := phi ((E) ⟨A z, sourceSurface_subset phi theta (A z).property⟩)
  continuous_toFun := by fun_prop

theorem exists_original_annulus_winding_correction
    {α : Type*} (e : α → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (theta : C512)
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (A : Ann ≃ₜ sourceSurface phi theta) (q : ℝ × ℝ → X)
    (hq : PolyhedralPLInCharts e q Ann) (hA : ∀ z : Ann, (A z : X) = q z)
    (hmarks : ∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
      (sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side)
        (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
          (by norm_num) (by norm_num) z) : X)) :
    ∃ (A' : Ann ≃ₜ sourceSurface phi theta) (q' : ℝ × ℝ → X),
      PolyhedralPLInCharts e q' Ann ∧ (∀ z : Ann, (A' z : X) = q' z) ∧
      (∀ side z, A' (Dehn.annulusRimPoint side z) = A (Dehn.annulusRimPoint side z)) ∧
      Nonempty ((sourceAnnulusHandleMap phi theta A').HomotopyRel
        (sourceAnnulusHandleMap (ContinuousMap.id H) theta (standardTargetAnnulus theta))
        Dehn.annulusRims) := by
  let J := standardAnnulusCylinderCoordinates
  let f : C(Ann, unitInterval × C32) :=
    ⟨fun z => J.symm (sourceAnnulusMap phi theta (A z)), by fun_prop⟩
  have hf : ∀ side z, f (Dehn.annulusRimPoint side z) = (if side then 1 else 0, z) := by
    intro side z
    have hmark : A (Dehn.annulusRimPoint side z) =
        sourceBoundaryCircle phi theta F (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
            (by norm_num) (by norm_num) z) := Subtype.ext (hmarks side z)
    change J.symm (sourceAnnulusMap phi theta (A (Dehn.annulusRimPoint side z))) = _
    rw [hmark, sourceAnnulusMap_boundaryCircle]
    exact J.symm_apply_eq.mpr (standardAnnulusCylinderCoordinates_rim side z).symm
  obtain ⟨T, hT, hTrims, ⟨HT⟩⟩ := Dehn.exists_annulus_winding_correction f hf
  obtain ⟨q', hq', hA'⟩ := exists_polyhedralPL_annulus_precomposition A q hq hA T hT
  let sectionMap : C(unitInterval × C32, H) := ⟨fun z => (Q).symm (J z, theta), by fun_prop⟩
  refine ⟨T.trans A, q', hq', hA', ?_, ⟨(HT.compContinuousMap sectionMap).cast ?_ ?_⟩⟩
  · intro side z
    change A (T (Dehn.annulusRimPoint side z)) = _
    rw [hTrims]
  · apply ContinuousMap.ext
    intro z
    change (Q).symm (J (J.symm (sourceAnnulusMap phi theta (A (T z)))), theta) = _
    rw [J.apply_symm_apply]
    let y : R := ⟨A (T z), sourceSurface_subset phi theta (A (T z)).property⟩
    have hy : (Q (phi ((E) y))).2 = theta :=
      (mem_sourceSurface_iff phi theta y).mp (A (T z)).property
    change (Q).symm ((Q (phi ((E) y))).1, theta) = phi ((E) y)
    rw [← hy, Prod.eta, (Q).symm_apply_apply]
  · apply ContinuousMap.ext
    intro z
    change (Q).symm (J (Dehn.annulusCylinderHomeomorph.symm z), theta) =
      (E) ((E).symm ((Q).symm (J (Dehn.annulusCylinderHomeomorph.symm z), theta)))
    rw [(E).apply_symm_apply]

end PoincareConjecture.M76.HamiltonIntervalTorus
