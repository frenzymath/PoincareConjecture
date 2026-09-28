import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.CollarDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.Tangential










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates




theorem ChartwisePLMap.exists_hamiltonZero_collar_tangential_adjustment
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (w : E → ℝ × ℝ) (hw : FinitePiecewiseAffineOn w J.space) :
    ∃ (psi : C(H0, H0)) (C : Set X0),
      IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x ∈ J.space, (Q0 (hamiltonZeroAmbientMap psi (c (x, 0)))).1 =
        ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1.1 + ((w x).1 : C0),
          (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1.2 + ((w x).2 : C0))) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  have hcover : ∀ x : X0, ∃ i, x ∈ (e i).source := by
    intro x
    exact hphi.source_domain.cover x
  obtain ⟨W, C, hC, hCU, hWPL, hWbase, hWnormal, hWzero⟩ :=
    exists_supported_original_collar_displacement e hphi.source_domain.compatible hcover
      J hJ hr c hc hi hopen w hw
  obtain ⟨G, hGvalue, hGzero, hGfixed, hGcircle, hGtangent,
    hpsi, H, Fpsi, hcircle⟩ :=
    hphi.exists_hamiltonZero_tangential_homotopy hd F W hWPL hWnormal hWzero
  let g : C(X0, X0) := ⟨fun x => G (1, x),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let psi := hamiltonZeroHandleMap g
  refine ⟨psi, C, hC, hCU, hpsi, H, Fpsi, ?_, hcircle, ?_, ?_⟩
  · refine ⟨{
      (hamiltonZeroHandleHomotopy phi G hGzero).toHomotopy with
      prop' := ?_ }⟩
    intro t x hx
    exact hamiltonZeroHandleHomotopy_fixed_exterior phi G hGzero hGfixed t x hx
  · intro x hx
    rw [hamiltonZeroAmbientMap_handle]
    exact hGfixed 1 x hx
  · intro x hx
    rw [hamiltonZeroAmbientMap_handle]
    change (Q0 (G (1, c (x, 0)))).1 = _
    rw [hGtangent, hWbase x hx]
    rfl

end PoincareConjecture.M76
