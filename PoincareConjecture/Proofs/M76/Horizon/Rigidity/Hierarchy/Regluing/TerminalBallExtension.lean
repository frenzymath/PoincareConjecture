import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.BoxBoundarySphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalCoordinatePL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallBoundaryExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.SurjectiveFundamentalGroup










set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "Cube" => closedBall (0 : V3) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLBall.exists_terminalBox_extension
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {P : Set X0}
    (ball : ChartwisePLBall e P (frontier P))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (boundaryMap : C(frontier P, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier P, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : E3).1.1) : C0), (((boundaryMap x : E3).1.2) : C0)),
        (((boundaryMap x : E3).2) : C0)))
    (hc : IsCoveringMap boundaryMap) :
    ∃ (H : ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ≃ₜ P) (f : E3 → X0),
      PolyhedralPLInCharts e f ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ∧
      (∀ z : ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta), f z = (H z : X0)) ∧
      (∀ z : ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta),
        f z ∈ frontier P ↔ (z : E3) ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
      ∀ x : frontier P,
        (H.symm ⟨x, ball.boundary_subset x.property⟩ : E3) = (boundaryMap x : E3) := by
  classical
  let Box : Set E3 := (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta
  let rb : Sphere ≃ₜ frontier P :=
    ball.parametrization.restrictSubsets sphere_subset_closedBall ball.boundary_subset
      (fun x => (ball.boundary_eq x).symm)
  have hrb (z : Sphere) : ball.map z = (rb z : X0) :=
    ball.map_eq ⟨z, sphere_subset_closedBall z.property⟩
  let : SimplyConnectedSpace Sphere := unitThreeSphere_lifting_properties.1
  let : SimplyConnectedSpace (frontier P) := rb.symm.toHomotopyEquiv.simplyConnectedSpace
  let : SimplyConnectedSpace (frontier Box) :=
    simplyConnectedSpace_terminalBox_frontier huv hab halpha
  let x0 : frontier P := rb ⟨fun _ => 1, by simp⟩
  have hsurj : Function.Surjective (FundamentalGroup.map
      ⟨boundaryMap, hc.continuous⟩ x0) := by
    intro g
    exact ⟨1, Subsingleton.elim _ _⟩
  let G : frontier P ≃ₜ frontier Box := hc.homeomorphOfFundamentalGroupMapSurjective x0 hsurj
  have hG (x : frontier P) : G x = boundaryMap x := rfl
  let HB : Sphere ≃ₜ frontier Box := rb.trans G
  let lift (z : V3) : E3 := if hz : z ∈ Sphere then HB ⟨z, hz⟩ else 0
  have hlift (z : Sphere) : lift z = (HB z : E3) := by
    simp only [lift, dif_pos z.property]
  have hcont : ContinuousOn lift Sphere := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp HB.continuous).congr (fun z => (hlift z).symm)
  have hclosed : IsClosed Box := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
  have hbox : MapsTo lift Sphere Box := by
    intro z hz
    rw [hlift ⟨z, hz⟩]
    exact hclosed.frontier_subset (HB ⟨z, hz⟩).property
  obtain ⟨J, hJ, hJS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsource : PolyhedralPLInCharts e ball.map J.space :=
    ball.piecewiseAffine.restrict_finite J hJ (hJS.subset.trans sphere_subset_closedBall)
  have hfinite : FinitePiecewiseAffineOn lift Sphere := by
    have h := hphi.finitePL_hamiltonZero_box_lift hd J hJ ball.map hsource
      huv hab halpha hthird hsecond hfirst lift
      (hcont.mono hJS.subset) (fun z hz => hbox (hJS.subset hz)) (by
        intro z hz
        have hzs : z ∈ Sphere := hJS.subset hz
        rw [hlift ⟨z, hzs⟩, hrb ⟨z, hzs⟩]
        exact hvalue (rb ⟨z, hzs⟩))
    exact hJS ▸ h
  let q (z : E3) : V3 := if hz : z ∈ frontier Box then HB.symm ⟨z, hz⟩ else 0
  have hq (z : frontier Box) : q z = (HB.symm z : V3) := by
    simp only [q, dif_pos z.property]
  have hleft : LeftInvOn q lift Sphere := by
    intro z hz
    rw [hlift ⟨z, hz⟩, hq (HB ⟨z, hz⟩), HB.symm_apply_apply]
  have himage : lift '' Sphere = frontier Box := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hlift ⟨z, hz⟩]
      exact (HB ⟨z, hz⟩).property
    · intro z hz
      refine ⟨HB.symm ⟨z, hz⟩, (HB.symm ⟨z, hz⟩).property, ?_⟩
      rw [hlift, HB.apply_symm_apply]
  have hqPL : FinitePiecewiseAffineOn q (frontier Box) := himage ▸ hfinite.inverse hleft
  have hqCube : MapsTo q (frontier Box) Cube := by
    intro z hz
    rw [hq ⟨z, hz⟩]
    exact sphere_subset_closedBall (HB.symm ⟨z, hz⟩).property
  have hqCopy := hqPL
  obtain ⟨K, hK, hKB, _⟩ := hqCopy
  let fbd : E3 → X0 := ball.map ∘ q
  have hfbd : PolyhedralPLInCharts e fbd (frontier Box) := by
    have h := ball.piecewiseAffine.comp_finitePiecewiseAffineOn K hK
      (hKB.symm ▸ hqPL) (fun z hz => hqCube (hKB.subset hz))
    exact hKB ▸ h
  have hfbdval (z : frontier Box) : (G.symm z : X0) = fbd z := by
    change (G.symm z : X0) = ball.map (q z)
    rw [hq z, hrb]
    change (G.symm z : X0) = (rb (rb.symm (G.symm z)) : X0)
    rw [rb.apply_symm_apply]
  have hpair := ((isFinitePLBallPair_Icc huv).prod
    (isFinitePLBallPair_Icc hab)).prod (isFinitePLBallPair_Icc halpha)
  have hfront := hpair.frontier_eq_of_finrank_eq rfl
  rw [← hfront] at hpair
  obtain ⟨H, f, hf, hfval, hfbdEq, hmem⟩ := ball.exists_prescribed_boundary_extension
    hphi.source_domain.compatible hpair K hK hKB G.symm fbd hfbd hfbdval
  refine ⟨H, f, hf, hfval, hmem, ?_⟩
  intro x
  have hz := (boundaryMap x).property
  have hforward : H ⟨boundaryMap x, hclosed.frontier_subset hz⟩ =
      ⟨x, ball.boundary_subset x.property⟩ := by
    apply Subtype.ext
    rw [← hfval, hfbdEq hz, ← hfbdval]
    change (G.symm (G x) : X0) = (x : X0)
    rw [G.symm_apply_apply]
  exact congrArg Subtype.val (H.symm_apply_eq.mpr hforward.symm)

end PoincareConjecture.M76
