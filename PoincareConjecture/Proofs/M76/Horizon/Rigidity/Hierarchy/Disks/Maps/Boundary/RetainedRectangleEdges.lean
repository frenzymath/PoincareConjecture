import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Elimination

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => Metric.closedBall (0 : V2) 1
local notation "Q" => Metric.sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem HamiltonZeroSecondPhaseGeometry.frontier_rectangle_edges
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi : C(H0, H0)} {a b alpha beta : ℝ}
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (hfirst : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (side : Bool) :
    let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    ∀ x ∈ frontier N,
      hamiltonZeroCircleMap phi x ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap phi x ∈
        ({((if side then b else a : ℝ) : C0), ((if side then a + p else b : ℝ) : C0)} : Set C0) := by
  dsimp only
  intro x hx
  rw [(geometry.slabs side).2.1] at hx
  rcases hx with hx | hx | hx
  · exact Or.inl (hfirst hx.2)
  · right
    have h : hamiltonZeroSecondCircleMap phi x = (a : C0) := hx.2
    cases side <;> simp [h]
  · right
    have h : hamiltonZeroSecondCircleMap phi x = (b : C0) := hx.2
    cases side <;> simp [h]

theorem hamiltonZero_retained_third_disk_rim_rectangle_edges
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi psi : C(H0, H0)} {a b alpha beta : ℝ}
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b)
    (hfirst : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (side : Bool)
    (G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi)
      (interior (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)))ᶜ)
    (j : V2 → X0)
    (hrim : ∀ z ∈ Q, j z ∈ frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) :
    ∀ z ∈ Q,
      hamiltonZeroCircleMap psi (j z) ∈ ({(alpha : C0), (beta : C0)} : Set C0) ∨
      hamiltonZeroSecondCircleMap psi (j z) ∈
        ({((if side then b else a : ℝ) : C0), ((if side then a + p else b : ℝ) : C0)} : Set C0) := by
  intro z hz
  have hval := G.fst_eq_snd (hrim z hz).2
  have hq1 : hamiltonZeroCircleMap psi (j z) = hamiltonZeroCircleMap phi (j z) := by
    exact congrArg (fun x => (hamiltonZeroHierarchyCoordinates (hamiltonZeroAmbientEquiv x)).2)
      hval.symm
  have hq2 : hamiltonZeroSecondCircleMap psi (j z) = hamiltonZeroSecondCircleMap phi (j z) := by
    rw [hamiltonZeroSecondCircleMap_ambient, ← hval, ← hamiltonZeroSecondCircleMap_ambient]
  rw [hq1, hq2]
  exact geometry.frontier_rectangle_edges hfirst side (j z) (hrim z hz)

end PoincareConjecture.M76
