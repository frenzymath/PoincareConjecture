import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.OriginalBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : V1) 1
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Q2" => sphere (0 : V2) 1

theorem exists_sourceRimCircle_finitePL_parametrization
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : V1)‖ = 1)
    (F : X → E)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F (sourceSurface phi theta)) :
    ∃ (j : Q2 ≃ₜ sourceRimCircle phi theta F0 b)
      (J : Q2 ≃ₜ Set.range (fun z : sourceRimCircle phi theta F0 b => F (z.val : X))),
      J.IsFinitePL ∧ J.symm.IsFinitePL ∧
      ∀ x : Q2, (J x : E) = F ((j x).val : X) := by
  obtain ⟨j, q, hq, hj⟩ :=
    exists_sourceRimCircle_polyhedral_parametrization hd phi hphi theta F0 b hb
  obtain ⟨K, hK, hKs⟩ := exists_finite_hamiltonMeridianRim
  have hPL : FinitePiecewiseAffineOn (F ∘ q) Q2 := by
    have hqK : PolyhedralPLInCharts e q K.space := hKs.symm ▸ hq
    simpa only [hKs] using hqK.finitePiecewiseAffineOn_comp K hK hF
  have hqi : InjOn (F ∘ q) Q2 := by
    intro x hx y hy hxy
    have hxy' : F ((j ⟨x, hx⟩).val : X) = F ((j ⟨y, hy⟩).val : X) := by
      simpa only [hj, Function.comp_apply] using hxy
    have hxy'' := hFi (j ⟨x, hx⟩).val.property.1 (j ⟨y, hy⟩).val.property.1 hxy'
    have hz : j ⟨x, hx⟩ = j ⟨y, hy⟩ := Subtype.ext (Subtype.ext hxy'')
    exact congrArg Subtype.val (j.injective hz)
  obtain ⟨J0, _, hJ0⟩ := hPL.exists_homeomorph_image hqi
  have himage : (F ∘ q) '' Q2 =
      Set.range (fun z : sourceRimCircle phi theta F0 b => F (z.val : X)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨j ⟨x, hx⟩, congrArg F (hj ⟨x, hx⟩)⟩
    · rintro ⟨z, rfl⟩
      refine ⟨j.symm z, (j.symm z).property, ?_⟩
      rw [Function.comp_apply, ← hj, j.apply_symm_apply]
  let J := J0.trans (Homeomorph.setCongr himage)
  have hJ : J.IsFinitePL := ⟨F ∘ q, hPL, hJ0⟩
  refine ⟨j, J, hJ, hJ.symm, ?_⟩
  intro x
  exact (hJ0 x).trans (congrArg F (hj x).symm)

end PoincareConjecture.M76.HamiltonIntervalTorus
