import PoincareLib.AlgebraicTopology.SingularHomology.Orientation.IntegralManifoldOrientation
import PoincareLib.Topology.Manifold.EmbeddedSphere.Parity.Equiv
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant parity of supported homology classes

The local integral homology atlas already constructed in M02 identifies
nearby point restrictions with the same integer. Divisibility by two is
independent of the chosen local frame, including on non-orientable manifolds.
This follows Hatcher, *Algebraic Topology*, Section 3.3, pp. 233-235, and
derivation 02 in `proof-work/tasks/M53/derivations/`. It is a step toward the
separation repair for Morgan--Tian Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Topology.EmbeddedSphere

open Poincare.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] {d : Nat}

/-- The parity of the point restrictions of one supported homology class is
locally constant on its support. No orientability or compactness is assumed.
Source: Hatcher pp. 233-235 and M53 derivation 02. -/
theorem isLocallyConstant_even_integralSupportRestriction
    (A : IntegralLocalHomologyAtlas X d) (K : Set X)
    (a : integralSupportHomology K d) :
    IsLocallyConstant (fun x : K =>
      Even (integralSupportHomologyRestriction (singleton_subset_iff.mpr x.property) d a)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let ax := integralSupportHomologyRestriction
    (singleton_subset_iff.mpr x.property) d a
  let m : Int := (A.localFrame x x (A.mem_baseSet x)).symm ax
  let b := A.basis x m
  have hxS : (x : X) ∈ A.support x := A.baseSet_subset_support x (A.mem_baseSet x)
  have hax : ax = integralSupportHomologyRestriction
      (singleton_subset_iff.mpr hxS) d b := by
    change ax = A.localFrame x x (A.mem_baseSet x) m
    exact ((A.localFrame x x (A.mem_baseSet x)).apply_symm_apply ax).symm
  obtain ⟨V, hV, hxV, heq⟩ := exists_open_integralSupportHomology_restrictions_eq
    K (A.support x) d a b x x.property hxS hax
  let U : Set K := (Subtype.val : K → X) ⁻¹' (A.baseSet x ∩ V)
  refine ⟨U, ((A.isOpen_baseSet x).inter hV).preimage continuous_subtype_val,
    ⟨A.mem_baseSet x, hxV⟩, ?_⟩
  intro y hy
  apply propext
  have hyS : (y : X) ∈ A.support x := A.baseSet_subset_support x hy.1
  have hey := heq y ⟨⟨y.property, hyS⟩, hy.2⟩
  have hby : integralSupportHomologyRestriction
      (singleton_subset_iff.mpr hyS) d b = A.localFrame x y hy.1 m := rfl
  change Even (integralSupportHomologyRestriction
    (singleton_subset_iff.mpr y.property) d a) ↔ Even ax
  rw [hey, hby]
  have hxframe : A.localFrame x x (A.mem_baseSet x) m = ax :=
    (A.localFrame x x (A.mem_baseSet x)).apply_symm_apply ax
  rw [← hxframe]
  exact ((A.localFrame x y hy.1).toAddEquiv.even_apply_iff m).trans
    ((A.localFrame x x (A.mem_baseSet x)).toAddEquiv.even_apply_iff m).symm

/-- A supported class has the same local parity at any two points of a
preconnected support. Source: the local homology covering in Hatcher,
printed p. 235, and the connected-support argument in M53 derivation 02. -/
theorem even_integralSupportRestriction_iff_of_isPreconnected
    (A : IntegralLocalHomologyAtlas X d) (K : Set X) (hK : IsPreconnected K)
    (a : integralSupportHomology K d) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    Even (integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) d a) ↔
      Even (integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) d a) := by
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  exact Iff.of_eq
    ((isLocallyConstant_even_integralSupportRestriction A K a).apply_eq_of_preconnectedSpace
      ⟨x, hx⟩ ⟨y, hy⟩)

/-- On a three-manifold, the required local homology atlas is supplied by
M02, so equal parity on a preconnected support requires no orientation
hypothesis. Source: Hatcher pp. 233-235 and M53 derivation 02. -/
theorem even_threeManifoldSupportRestriction_iff_of_isPreconnected
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (K : Set X) (hK : IsPreconnected K) (a : integralSupportHomology K 3)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    Even (integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3 a) ↔
      Even (integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 a) := by
  obtain ⟨A⟩ := exists_integralThreeLocalHomologyAtlas (X := X)
  exact even_integralSupportRestriction_iff_of_isPreconnected A K hK a hx hy

end PoincareMT.Topology.EmbeddedSphere
