import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.InteriorPhaseCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.SourceSlab



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))

theorem sourceSurface_eq_inter_phase (phi : C(H, H)) (c : C) :
    sourceSurface phi c = R ∩ ambientSourcePhase phi ⁻¹' {c} := by
  ext x
  constructor
  · intro hx
    have hR := sourceSurface_subset phi c hx
    exact ⟨hR, (ambientSourcePhase_domain phi ⟨x, hR⟩).trans
      ((mem_sourceSurface_iff phi c ⟨x, hR⟩).mp hx)⟩
  · rintro ⟨hR, hx⟩
    exact (mem_sourceSurface_iff phi c ⟨x, hR⟩).mpr
      ((ambientSourcePhase_domain phi ⟨x, hR⟩).symm.trans hx)

theorem sourceSlab_eq_inter_phase (phi : C(H, H)) (a b : ℝ) :
    sourceSlab phi a b = R ∩ ambientSourcePhase phi ⁻¹'
      AddCircle.closedIntervalArc (4 * 128) a b := by
  ext x
  constructor
  · intro hx
    have hR := sourceSlab_subset phi a b hx
    refine ⟨hR, ?_⟩
    change ambientSourcePhase phi x ∈ AddCircle.closedIntervalArc (4 * 128) a b
    rw [ambientSourcePhase_domain phi ⟨x, hR⟩]
    exact (mem_sourceSlab_iff phi a b ⟨x, hR⟩).mp hx
  · rintro ⟨hR, hx⟩
    apply (mem_sourceSlab_iff phi a b ⟨x, hR⟩).mpr
    rwa [← ambientSourcePhase_domain phi ⟨x, hR⟩]

end PoincareConjecture.M76.HamiltonIntervalTorus
