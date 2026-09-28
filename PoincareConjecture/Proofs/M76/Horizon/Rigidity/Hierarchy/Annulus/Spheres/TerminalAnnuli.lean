import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Elimination
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.CompressedComponentAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.RetainedRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_terminal_component_annuli
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi0 psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi0 x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi0 (theta : C0))
    (geometry : HamiltonZeroSecondPhaseGeometry e R psi a b)
    (hcover : ∀ theta ∈ ({a, b} : Set ℝ),
      IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi0 (frontier R) theta))
    (hterminal : ∀ theta ∈ ({a, b} : Set ℝ), ∀ T : Set X0, T.Nonempty →
      T ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
      (∀ x ∈ T, connectedComponentIn
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = T) →
      (T ∩ frontier R).Nonempty) :
    ∀ theta ∈ ({a, b} : Set ℝ), ∀ T : Set X0, T.Nonempty →
      T ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
      (∀ x ∈ T, connectedComponentIn
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = T) →
      ∃ H : squareAnnulus 8 1 ≃ₜ T, ∃ f : (ℝ × ℝ) → X0,
        PolyhedralPLInCharts e f (squareAnnulus 8 1) ∧
        (∀ z : squareAnnulus 8 1, f z = (H z : X0)) ∧
        ∀ z : squareAnnulus 8 1,
          depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
            (H z : X0) ∈ frontier R := by
  have hne : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  intro theta htheta T hTne hT hcomponent
  have hrim := hterminal theta htheta T hTne hT hcomponent
  obtain ⟨x, _, hnontrivial⟩ := exists_nontrivial_hamiltonZero_retained_phase_component
    phi0 psi heR.closed hAR hfixed theta (hcover theta htheta) hT hcomponent hrim
  let : Nontrivial (FundamentalGroup T x) := hnontrivial
  let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
  let y : S := (ContinuousMap.inclusion hT) x
  let : IsCyclic (FundamentalGroup C0 (hamiltonZeroSecondPhaseCircleMap psi R theta y)) :=
    HamiltonIntervalTorus.circleFundamentalGroup_isCyclic p (by norm_num) _
  let : IsCyclic (FundamentalGroup S y) := isCyclic_of_injective
    (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R theta) y)
    (geometry.groups theta htheta y).2
  let : IsCyclic (FundamentalGroup T x) := isCyclic_of_injective
    (FundamentalGroup.map (ContinuousMap.inclusion hT) x)
    (FundamentalGroup.inclusion_injective_of_whole_component hT hcomponent x)
  rcases htheta with rfl | rfl
  · exact exists_hamiltonZero_compressed_component_annulus e phi0 psi heR hA hAR hfixed
      hne (hreg _ (Or.inl rfl)) (geometry.slabs false).1 (geometry.slabs false).2.1
      T hT hcomponent hrim x
  · exact exists_hamiltonZero_compressed_component_annulus e phi0 psi heR hA hAR hfixed
      hne.symm (hreg _ (Or.inr rfl)) (geometry.slabs false).1
      (by simpa only [union_comm] using (geometry.slabs false).2.1)
      T hT hcomponent hrim x

end PoincareConjecture.M76
