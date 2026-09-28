import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.PeriodDescent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimCircles
import PoincareConjecture.Proofs.M76.Rigidity.SourceBoundaryCylinder
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : V1) 1
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Q2" => sphere (0 : V2) 1

theorem polyhedralPL_sourceBoundaryCircle_period
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : V1)‖ = 1) :
    PolyhedralPLInCharts e
      (fun t : ℝ => (sourceBoundaryCircle phi theta F b hb ((512 * t : ℝ) : C) : X))
      (Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨r, rfl⟩ := Quotient.exists_rep theta
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (a := (0 : ℝ)) (b := 1) zero_lt_one
  let w : (Fin 1 ⊕ Fin 2) → ℝ := Sum.elim (fun _ => 0) ![512, 0]
  let a : ℝ →ᴬ[ℝ] ((Fin 1 ⊕ Fin 2) → ℝ) :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight w).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ ℝ (Sum.elim (b : V1) ![0, r])
  let q : ℝ → R := fun t => ⟨((b : V1), QuotientAddGroup.mk ![512 * t, r]),
    b.property, mem_univ _⟩
  have hqval (t : ℝ) : (q t : X) =
      (sourceBoundaryCircle phi (r : C) F b hb ((512 * t : ℝ) : C) : X) := by
    rw [sourceBoundaryCircle_original_point, hamiltonOneHierarchyCoordinates_symm_coe]
    rfl
  have hproj : latticeCoordinateProjection (Fin 1) (Fin 2) L ∘ a =
      fun t => (q t : X) := by
    funext t
    apply Prod.ext
    · funext i
      simp [latticeCoordinateProjection, a, w, q]
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> simp [a, w, mul_comm]
  have hqPL : PolyhedralPLInCharts d (fun t => (q t : X)) K.space := by
    rw [← hproj]
    exact hd.polyhedralPL_projection ((K.affineOnFaces_affine a).finitePiecewiseAffineOn hK)
  have hq : Continuous q := by
    apply Continuous.subtype_mk
    apply continuous_const.prodMk
    apply QuotientAddGroup.continuous_mk.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hqB : MapsTo q K.space ((Subtype.val : R → X) ⁻¹' frontier R) := by
    intro t ht
    rw [mem_preimage, hqval]
    exact sourceBoundaryCircle_mem_frontier phi (r : C) F b hb _
  have hfix (x : R) (hx : (x : X) ∈ frontier R) :
      latticeHandleMapInDomain (Fin 1) (Fin 2) L phi x = x :=
    ((latticeHandleMapInDomain_homotopyRel (Fin 1) (Fin 2) L phi F).fst_eq_snd hx).symm
  have h := hphi.polyhedralPLInCharts_boundary_fixed hfix K hK q hq.continuousOn hqB hqPL
  rw [hKs] at h
  exact h.congr (fun t _ => hqval t)

theorem exists_sourceRimCircle_polyhedral_parametrization
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : V1)‖ = 1) :
    ∃ (j : Q2 ≃ₜ sourceRimCircle phi theta F b) (q : V2 → X),
      PolyhedralPLInCharts e q Q2 ∧ ∀ x : Q2, ((j x).val : X) = q x := by
  let scale : C32 ≃ₜ C := AddCircle.homeomorphAddCircle
    (4 * (8 : ℝ)) (4 * (128 : ℝ)) (by norm_num) (by norm_num)
  have hscale (t : ℝ) : scale ((32 * t : ℝ) : C32) = ((512 * t : ℝ) : C) := by
    rw [AddCircle.homeomorphAddCircle_apply_mk]
    congr 1
    norm_num
    ring
  let f : C32 → X := fun c => sourceBoundaryCircle phi theta F b hb (scale c)
  have hperiod : PolyhedralPLInCharts e
      (fun t : ℝ => f ((32 * t : ℝ) : C32)) (Icc (0 : ℝ) 1) := by
    exact (polyhedralPL_sourceBoundaryCircle_period hd phi hphi theta F b hb).congr
      (fun t _ => by simp only [f, hscale])
  obtain ⟨j, q, hq, hjq⟩ := exists_square_rim_map_of_PL_period e
    hphi.source_domain.compatible f hperiod
  refine ⟨j.symm.trans (scale.trans (sourceRimCircleCoordinates phi theta F b hb)),
    q, hq, ?_⟩
  intro x
  have h := hjq (j.symm x)
  rw [j.apply_symm_apply] at h
  exact h.symm

end PoincareConjecture.M76.HamiltonIntervalTorus
