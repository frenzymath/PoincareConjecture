import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Maps.SupportedBallArc
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.ClosedArcBoundaryLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.HandleInjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.InteriorPhaseCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.SourceSurface
import PoincareConjecture.Proofs.M76.Rigidity.StandardBoundaryTori

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "Q" => hamiltonOneHierarchyCoordinates
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_original_ball_phase_removal
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    {D S : Set X} (b : ChartwisePLBall e D S) (hDR : D ⊆ interior R)
    (lower upper : ℝ) (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < p)
    (hboundary : ∀ x ∈ S, ambientSourcePhase phi x ∈
      ((↑) : ℝ → C) '' Icc lower upper) :
    ∃ (psi : C(H, H)) (T : phi.HomotopyRel psi B),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      (∀ (t : unitInterval) (x : H), ((E).symm x : X) ∉ interior D → T (t, x) = phi x) ∧
      (∀ (t : unitInterval) (x : H), (Q (T (t, x))).1 = (Q (phi x)).1) ∧
      psi ⁻¹' B = phi ⁻¹' B ∧
      (∀ x : H, ((E).symm x : X) ∈ D →
        sourcePhase psi x ∈ ((↑) : ℝ → C) '' Icc lower upper) ∧
      ∀ theta : C, theta ∉ ((↑) : ℝ → C) '' Icc lower upper →
        sourceSurface psi theta = sourceSurface phi theta \ D := by
  let f : C(X, H) := phi.comp ((⟨E, (E).continuous⟩ : C(R, H)).comp handleAmbientRetraction)
  have hf (x : R) : f x = phi (E x) := by
    change phi (E (handleAmbientRetraction (x : X))) = _
    rw [handleAmbientRetraction_apply_coe]
  let q : C({x : D | (x : X) ∈ S}, C) :=
    ⟨fun x => (Q (f x)).2, by fun_prop⟩
  obtain ⟨boundary, hboundaryQ, hboundaryRange⟩ :=
    AddCircle.exists_lift_in_closed_arc p q lower upper hlower hupper (by
      intro x
      have hxR : (x.val : X) ∈ R := interior_subset (hDR x.val.property)
      change (Q (f (⟨x.val, hxR⟩ : R))).2 ∈ _
      rw [hf]
      change sourcePhase phi (E ⟨x.val, hxR⟩) ∈ _
      rw [← ambientSourcePhase_domain]
      exact hboundary x x.property)
  obtain ⟨g, W, hWcoord, hgchoice, hgrange⟩ :=
    exists_supported_ball_phase_clamp b f boundary hboundaryQ lower upper horder hboundaryRange
  let j : C(H, X) := ⟨fun x => ((E).symm x : X), by fun_prop⟩
  have hfj (x : H) : f (j x) = phi x := by
    change f ((E).symm x : X) = _
    rw [hf, (E).apply_symm_apply]
  let psi : C(H, H) := g.comp j
  have hB (x : H) (hx : x ∈ B) : j x ∉ interior D := by
    have hxF : j x ∈ frontier R := by
      apply (Set.ext_iff.mp
        (latticeHandleDomainEquiv_preimage_boundary (Fin 1) (Fin 2) L) ((E).symm x)).mp
      simpa using hx
    exact fun h => disjoint_left.mp disjoint_interior_frontier (hDR (interior_subset h)) hxF
  let T : phi.HomotopyRel psi B := {
    toFun := fun z => W (z.1, j z.2)
    continuous_toFun := W.continuous_toFun.comp
      (continuous_fst.prodMk (j.continuous.comp continuous_snd))
    map_zero_left := fun x => (W.apply_zero (j x)).trans (hfj x)
    map_one_left := fun x => W.apply_one (j x)
    prop' := fun t x hx => (W.eq_fst t (hB x hx)).trans (hfj x) }
  have hchoice (x : H) : psi x = phi x ∨
      psi x = handlePhaseRetraction lower (phi x) ∨
      psi x = handlePhaseRetraction upper (phi x) := by
    change g (j x) = phi x ∨ g (j x) = handlePhaseRetraction lower (phi x) ∨
      g (j x) = handlePhaseRetraction upper (phi x)
    simpa only [hfj] using hgchoice (j x)
  have hfixed (t : unitInterval) (x : H) (hx : j x ∉ interior D) :
      T (t, x) = phi x := (W.eq_fst t hx).trans (hfj x)
  have hrange (x : H) (hx : j x ∈ D) :
      sourcePhase psi x ∈ ((↑) : ℝ → C) '' Icc lower upper := hgrange (j x) hx
  refine ⟨psi, T, chartwisePL_of_targetPhaseSelection hd hphi lower upper psi hchoice,
    hfixed, ?_, ?_, hrange, ?_⟩
  · intro t x
    exact (hWcoord t (j x)).trans (congrArg (fun z : H => (Q z).1) (hfj x))
  · ext x
    exact targetPhaseSelection_boundary_iff hchoice x
  · intro theta htheta
    ext x
    constructor
    · intro hx
      have hxR := sourceSurface_subset psi theta hx
      let xR : R := ⟨x, hxR⟩
      have hphase := (mem_sourceSurface_iff psi theta xR).mp hx
      have hxD : x ∉ D := by
        intro hxD
        apply htheta
        rw [← hphase]
        apply hrange (E xR)
        simpa only [j, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] using hxD
      have hfix : psi (E xR) = phi (E xR) :=
        (T.apply_one _).symm.trans (hfixed 1 _ (by
          simpa only [j, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] using
            (fun hi => hxD (interior_subset hi))))
      refine ⟨(mem_sourceSurface_iff phi theta xR).mpr ?_, hxD⟩
      change (Q (phi (E xR))).2 = theta
      change (Q (psi (E xR))).2 = theta at hphase
      rwa [hfix] at hphase
    · rintro ⟨hx, hxD⟩
      let xR : R := ⟨x, sourceSurface_subset phi theta hx⟩
      have hfix : psi (E xR) = phi (E xR) :=
        (T.apply_one _).symm.trans (hfixed 1 _ (by
          simpa only [j, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply] using
            (fun hi => hxD (interior_subset hi))))
      apply (mem_sourceSurface_iff psi theta xR).mpr
      change (Q (psi (E xR))).2 = theta
      rw [hfix]
      exact (mem_sourceSurface_iff phi theta xR).mp hx

end PoincareConjecture.M76.HamiltonIntervalTorus
