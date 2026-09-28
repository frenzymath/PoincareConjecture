import PoincareConjecture.Proofs.M76.Rigidity.MeridianComplementCylinder
import PoincareConjecture.Proofs.M76.Rigidity.SourceBoundaryCylinder









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))



theorem polyhedralPL_source_hamiltonComplementCylinder
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a : ℝ} (ha : 0 < a) (hap : a < p / 2) :
    PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap (Q ×ˢ Icc a (p - a)) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand
    (a := a) (b := p - a) (by linarith)
  have hsub : K.space ⊆ Q ×ˢ Icc (0 : ℝ) p := by
    rw [hKS]
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have h := (polyhedralPL_source_hamiltonBoundaryCylinder hd phi hphi F).restrict_finite
    K hK hsub
  rwa [hKS] at h

end PoincareConjecture.M76
