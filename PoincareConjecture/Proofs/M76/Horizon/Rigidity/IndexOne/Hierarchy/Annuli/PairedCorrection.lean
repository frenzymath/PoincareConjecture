import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.WholeAnnuli
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.SourceCorrection










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Ann" => squareAnnulus 8 1



theorem exists_relative_corrected_whole_source_annuli
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (hI : IsPLIrreducible e R)
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (eta : C(H, H)) (K : Set X) (Feta : (ContinuousMap.id H).HomotopyRel eta B),
        IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ K →
          eta x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L eta) ∧
        Nonempty (phi.HomotopyRel eta B) ∧ eta ⁻¹' B = phi ⁻¹' B ∧
        PairedSourceGeometry e eta a b ∧
        (∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          IsPLIrreducible e (sourceSlab eta uv.1 uv.2)) ∧
        ∀ theta ∈ ({a, b} : Set ℝ),
          ∃ (A : Ann ≃ₜ sourceSurface eta (theta : C)) (q : ℝ × ℝ → X),
            PolyhedralPLInCharts e q Ann ∧ (∀ x : Ann, (A x : X) = q x) ∧
            (∀ side z, (A (Dehn.annulusRimPoint side z) : X) =
              (sourceBoundaryCircle eta (theta : C) Feta (originalIntervalEndpoint side)
                (originalIntervalEndpoint_norm side)
                (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) p
                  (by norm_num) (by norm_num) z) : X)) ∧
            Nonempty ((sourceAnnulusHandleMap eta (theta : C) A).HomotopyRel
              (sourceAnnulusHandleMap (ContinuousMap.id H) (theta : C)
                (standardTargetAnnulus (theta : C))) Dehn.annulusRims) := by
  obtain ⟨a, ha, b, hb, eta, K, Feta, hK, hKR, hfixed, heta, Heta, hB,
      geometry, hirr, hannuli⟩ :=
    exists_relative_whole_source_annuli e d hd phi hphi hI F0
  refine ⟨a, ha, b, hb, eta, K, Feta, hK, hKR, hfixed, heta, Heta, hB,
    geometry, hirr, ?_⟩
  intro theta htheta
  obtain ⟨A, q, hq, hA, hmarks⟩ := hannuli theta htheta
  obtain ⟨A', q', hq', hA', hmarks', hhom⟩ :=
    exists_original_annulus_winding_correction e eta (theta : C) Feta A q hq hA hmarks
  refine ⟨A', q', hq', hA', ?_, hhom⟩
  intro side z
  rw [hmarks']
  exact hmarks side z

end PoincareConjecture.M76.HamiltonIntervalTorus
