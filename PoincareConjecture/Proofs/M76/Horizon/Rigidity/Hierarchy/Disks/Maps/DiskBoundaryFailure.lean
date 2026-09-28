import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.DiskFailureArc

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

def HamiltonZeroDiskFailureArc {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (phi : C(H0, H0)) (j : V2 → X0) (theta : C0)
    (alpha beta a b : ℝ) : Prop :=
  ∃ (param : ℝ → V2) (k : C(unitInterval, X0)),
    FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1) ∧
    PolyhedralPLInCharts e (j ∘ param) (Icc (0 : ℝ) 1) ∧
    (∀ t : unitInterval, param t ∈ D ∧ j (param t) = k t) ∧
    Topology.IsEmbedding k ∧ k 0 ≠ k 1 ∧ range k ⊆ j '' D ∧
    (∀ t, k t ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
    (∀ t, k t ∈ interior R ↔ t ≠ 0 ∧ t ≠ 1) ∧
    ∃ F : ((hamiltonZeroAmbientMap phi).comp k).HomotopyRel
        (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (k 0)))
        ({0, 1} : Set unitInterval),
      ∀ s t, (Q0 (F (s, t))).1.1 = theta ∧
        (Q0 (F (s, t))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
        (Q0 (F (s, t))).1.2 ∈ AddCircle.closedIntervalArc p a b

theorem exists_hamiltonZero_disk_failure_arc_of_not_injective_rim
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R : Set X0} (hR : IsClosed R)
    (j : V2 → X0) (hj : PolyhedralPLInCharts e j D)
    (hi : Topology.IsEmbedding (fun z : D => j z)) (hjR : MapsTo j D R)
    (hrim : ∀ z : D, (z : V2) ∈ Q ↔ j z ∈ frontier R)
    {cut alpha beta cut' a b : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (ha : cut' < a) (hb : b < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (theta : C0) (hthird : ∀ z : D, hamiltonZeroThirdCircleMap phi (j z) = theta)
    (hnot : ¬ InjOn (fun z => hamiltonZeroAmbientMap phi (j z)) Q) :
    HamiltonZeroDiskFailureArc e R phi j theta alpha beta a b := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let f : C(D, j '' D) := ⟨fun z => ⟨j z, ⟨z, z.property, rfl⟩⟩,
    hj.continuousOn.domRestrict.subtype_mk _⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      exact hi.injective (congrArg (fun z : j '' D => (z : X0)) h)
    · rintro ⟨y, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let H : D ≃ₜ j '' D := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed
    f.continuous f.continuous.isClosedMap
  have hH (z : D) : (H z : X0) = j z := rfl
  simp only [InjOn] at hnot
  push Not at hnot
  obtain ⟨x, hx, y, hy, heq, hne⟩ := hnot
  obtain ⟨param, k, hparam, hjparam, hkval, hkemb, hk0, _, hkne, hkS, hkfront, hkint, F, hF⟩ :=
    exists_hamiltonZero_source_disk_failure_arc phi hR (image_subset_iff.mpr hjR) H j hj
      (fun z => (hH z).symm) (fun z => by rw [hH]; exact (hrim z).symm)
      halpha hbeta ha hb (fun z hz => hfirst (hjR hz))
      (fun z hz => hsecond (hjR hz)) theta (fun z hz => hthird ⟨z, hz⟩) x y hx hy hne heq
  refine ⟨param, k, hparam, hjparam, hkval, hkemb, hkne, hkS, hkfront, hkint, ?_⟩
  rw [hk0]
  exact ⟨F, hF⟩

end PoincareConjecture.M76
