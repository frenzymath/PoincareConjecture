import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianComplementaryPrism
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodRegluing










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))




theorem exists_source_meridian_rigidity
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hI : IsPLIrreducible e R) (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z)) (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (hrim : ∀ z ∈ Q, j z = hamiltonStandardMeridianMap L z) :
    ∃ g : H ≃ₜ H,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 2) (Fin 1) L g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel ⟨g, g.continuous⟩ B) := by
  obtain ⟨a, ha, hasmall, P, _hPU, hmark, _hopen, _heK, _hK, _hb,
    _hint, _hfront, _hoverlap, hcover, HP, u, hu, hvalue, _hboundary, _hmem,
    hlower, hupper, hlateral⟩ :=
    exists_source_meridian_complementary_prism hI hd phi hphi F
      j hj hemb hDR hproper hrim isOpen_univ (subset_univ _)
  have hgap : a / 2 < p - a / 2 := by linarith
  exact P.exists_period_PL_regluing hd hI.1 ha hgap HP u hu hvalue hlower hupper
    hmark hlateral hcover phi F

end PoincareConjecture.M76
