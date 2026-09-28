import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.Mathlib.Fiberwise
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.FiberwisePhaseMap










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZeroAmbientMap_isLocalHomeomorphOn_of_fiberwise_covering
    {E : Type*} [TopologicalSpace E] {S : Set E} {r : ℝ}
    (psi : C(H0, H0)) (c : E × ℝ → X0)
    (hi : Topology.IsEmbedding (fun z : S ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (S ×ˢ Ioo (-r) r)))
    (g : C(S, C0 × C0)) (hg : IsCoveringMap g)
    (theta : C0) {sigma : ℝ} (hsigma : sigma ≠ 0)
    (hproduct : ∀ x : S, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap psi (c (x, t))) =
        (g x, theta + ((sigma * t : ℝ) : C0))) :
    IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi) (c '' (S ×ˢ Ioo (-r) r)) :=
  PhaseCovering.isLocalHomeomorphOn_of_fiberwise_covering p Q0 c hi hopen
    (hamiltonZeroAmbientMap psi) g hg theta hsigma hproduct




theorem ChartwisePLMap.exists_hamiltonZero_covering_phase_adjustment
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
    (hopen : ∀ eps : ℝ, 0 < eps → eps ≤ r → IsOpen (c '' (J.space ×ˢ Ioo (-eps) eps)))
    (theta : C0) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (hproduct : ∀ x : J.space, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c (x, t))) =
        ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1, theta + ((sigma * t : ℝ) : C0)))
    (g : C(J.space, C0 × C0)) (hg : IsCoveringMap g)
    (H : (hamiltonZeroCollarTangentialMap phi J hr c hc).Homotopy g)
    (hgPL : PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J g theta) J.space) :
    ∃ (psi : C(H0, H0)) (C : Set X0),
      IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x : J.space, ∀ t ∈ Icc (-(r / 4)) (r / 4),
        Q0 (hamiltonZeroAmbientMap psi (c (x, t))) = (g x, theta + ((sigma * t : ℝ) : C0))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi)
        (c '' (J.space ×ˢ Ioo (-(r / 4)) (r / 4))) ∧
      IsLocalHomeomorphOn (hamiltonZeroAmbientMap psi) (c '' (J.space ×ˢ ({0} : Set ℝ))) := by
  obtain ⟨psi, C, hC, hCU, hpsi, Hpsi, Fpsi, Hexterior, hnormal, hfixed, hnew⟩ :=
    hphi.exists_hamiltonZero_fiberwise_phase_adjustment hd F J hJ hr c hc hi
      (hopen (r / 2) (by positivity) (by linarith)) theta sigma hproduct g H hgPL
  have hsub : J.space ×ˢ Icc (-(r / 4)) (r / 4) ⊆ J.space ×ˢ Icc (-r) r := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by dsimp only at ht ⊢; constructor <;> linarith [ht.1, ht.2]⟩
  have hlocal := hamiltonZeroAmbientMap_isLocalHomeomorphOn_of_fiberwise_covering
    (r := r / 4) psi c
    (hi.comp (Topology.IsEmbedding.inclusion hsub))
    (hopen (r / 4) (by positivity) (by linarith)) g hg theta hsigma hnew
  refine ⟨psi, C, hC, hCU, hpsi, Hpsi, Fpsi, Hexterior, hnormal, hfixed, hnew, hlocal,
    hlocal.mono (image_mono ?_)⟩
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  have ht0 : t = 0 := ht
  subst t
  exact ⟨hx, by constructor <;> linarith⟩

end PoincareConjecture.M76
