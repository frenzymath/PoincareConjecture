import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.WholeComponentAlternative









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_closed_third_component_sphere
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
    {R A : Set X0} (hI : IsPLIrreducible e R)
    (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroThirdCoordinateRegularity e R phi theta)
    {l r : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r))
    (hfront : frontier (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r) =
      ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p l r) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {other})))
    {c alpha beta d a b : ℝ}
    (halpha : c < alpha) (hbeta : beta < c + p)
    (ha : d < a) (hb : b < d + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hinj : ∀ x : ↥(R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}), X0)) x))
    {S : Set X0} (hSne : S.Nonempty)
    (hS : S ⊆ R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S,
      connectedComponentIn (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {theta}) x = S)
    (hrim : Disjoint S (frontier R)) :
    Nonempty (ChartwisePLSphere e S) := by
  obtain ⟨n, T, hcover, _, hprops⟩ :=
    exists_hamiltonZero_third_whole_component_alternatives e phi psi Fpsi hI
      hA hAR hfixed hne hreg hN hfront halpha hbeta ha hb hfirst hsecond hinj
  obtain ⟨x, hx⟩ := hSne
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm.subset (hS hx))
  have hTi : T i = S := ((hprops i).2.2.1 x hxi).symm.trans (hcomponent x hx)
  have halternative := (hprops i).2.2.2
  rw [hTi] at halternative
  rcases halternative with ⟨H, j, _, _, _, hjH, _, hproper⟩ | ⟨_, hsphere, _⟩
  · let z : D := ⟨Dehn.squareRimBase, sphere_subset_closedBall Dehn.squareRimBase.property⟩
    have hzR : j z ∈ frontier R := (hproper z).mpr Dehn.squareRimBase.property
    have hzS : j z ∈ S := hjH z ▸ (H z).property
    exact (disjoint_left.mp hrim hzS hzR).elim
  · exact hsphere

end PoincareConjecture.M76
