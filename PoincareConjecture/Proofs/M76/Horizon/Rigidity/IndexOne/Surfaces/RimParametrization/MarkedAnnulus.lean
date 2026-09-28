import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.OriginalBoundary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourceAnnulusMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.PrescribedRimChart



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem exists_annulus_chart_prescribed_source_rims
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    {S : Set X} (hS : S ⊆ sourceSurface phi theta)
    {T : Set E} (Hmodel : T ≃ₜ S)
    (hHF : ∀ x : S, (Hmodel.symm x : E) = F x)
    (a : Ann ≃ₜ T) (ha : a.IsFinitePL)
    (rim : Bool → Set E) (hrimT : ∀ side, rim side ⊆ T)
    (gamma : ∀ side, C ≃ₜ rim side)
    (hgamma : ∀ side z, (gamma side z : E) =
      F (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) z))
    (hsource : ∀ side z, (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side) z : X) ∈ S)
    (hrim : ∀ side (x : Ann), depth 8 (x : ℝ × ℝ) = (if side then 1 else -1) ↔
      (a x : E) ∈ rim side) :
    ∃ A : Ann ≃ₜ T, A.IsFinitePL ∧
      ∀ side z, (A (Dehn.annulusRimPoint side z) : E) =
        F (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
          (originalIntervalEndpoint_norm side)
          (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
            (by norm_num) (by norm_num) z)) := by
  let scale : C32 ≃ₜ C := AddCircle.homeomorphAddCircle
    (4 * (8 : ℝ)) (4 * (128 : ℝ)) (by norm_num) (by norm_num)
  have hscale (t : ℝ) : scale ((32 * t : ℝ) : C32) = ((512 * t : ℝ) : C) := by
    rw [AddCircle.homeomorphAddCircle_apply_mk]
    congr 1
    norm_num
    ring
  let gamma32 : ∀ side, C32 ≃ₜ rim side := fun side => scale.trans (gamma side)
  have hperiod (side : Bool) : FinitePiecewiseAffineOn
      (fun t : ℝ => (gamma32 side ((32 * t : ℝ) : C32) : E)) (Icc 0 1) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (a := (0 : ℝ)) (b := 1) zero_lt_one
    have hPL := polyhedralPL_sourceBoundaryCircle_period hd phi hphi theta F0
      (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side)
    have hPLK := hKs.symm ▸ hPL
    have hcomp := hPLK.finitePiecewiseAffineOn_comp K hK hF
    rw [hKs] at hcomp
    apply hcomp.congr
    intro t _
    change F _ = (gamma side (scale ((32 * t : ℝ) : C32)) : E)
    rw [hgamma, hscale]
  let radial : C(T, C32) := ⟨fun x => scale.symm
    ((sourceAnnulusMap phi theta (Set.inclusion hS (Hmodel x))).2), by fun_prop⟩
  have hradial (side : Bool) (z : C32) :
      radial ⟨gamma32 side z, hrimT side (gamma32 side z).property⟩ = z := by
    let y : S := ⟨sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side) (scale z), hsource side (scale z)⟩
    have hy : Hmodel.symm y =
        ⟨gamma32 side z, hrimT side (gamma32 side z).property⟩ := by
      apply Subtype.ext
      exact (hHF y).trans (hgamma side (scale z)).symm
    have hv : Hmodel ⟨gamma32 side z, hrimT side (gamma32 side z).property⟩ = y := by
      rw [← hy, Hmodel.apply_symm_apply]
    change scale.symm ((sourceAnnulusMap phi theta
      (Set.inclusion hS (Hmodel _))).2) = z
    rw [hv]
    change scale.symm ((sourceAnnulusMap phi theta
      (sourceBoundaryCircle phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) (scale z))).2) = z
    rw [sourceAnnulusMap_boundaryCircle, scale.symm_apply_apply]
  obtain ⟨A, hA, hAv⟩ := Dehn.exists_annulus_chart_prescribed_rims
    a ha rim hrimT gamma32 hperiod hrim radial hradial
  refine ⟨A, hA, ?_⟩
  intro side z
  exact (hAv side z).trans (hgamma side (scale z))

end PoincareConjecture.M76.HamiltonIntervalTorus
