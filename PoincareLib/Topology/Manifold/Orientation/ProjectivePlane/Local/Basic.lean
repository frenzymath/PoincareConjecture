import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Homology.Local
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally represented integral orientations

The orientation is an actual family of local integral homology generators,
locally obtained by restricting one support class. This is Hatcher's
definition in Section 3.3, pp. 233-235, used in Morgan--Tian Theorem 0.3,
footnote 2, printed p. xii.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set Filter
open scoped Topology

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

/-- A topological orientation in dimension three, expressed using actual
local integral homology. Source: Hatcher, Section 3.3, p. 234. -/
structure LocalOrientation (X : Type u) [TopologicalSpace X] where
  /-- The chosen generator at each point. -/
  atPoint : ∀ x : X, LocalHomology X x 3
  /-- Each point class is an integral generator. -/
  generates : ∀ x : X, ∃ e : Int ≃ₗ[Int] LocalHomology X x 3, e 1 = atPoint x
  /-- Nearby point classes come from one support class. -/
  locallyRepresented : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = atPoint y

namespace LocalOrientation

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A chosen basis realizing a local generator. Source: Hatcher, p. 234. -/
def basis (O : LocalOrientation X) (x : X) : Int ≃ₗ[Int] LocalHomology X x 3 :=
  (O.generates x).choose

/-- The chosen basis has the specified generator. Source: Hatcher, p. 234. -/
@[simp]
theorem basis_one (O : LocalOrientation X) (x : X) : O.basis x 1 = O.atPoint x :=
  (O.generates x).choose_spec

/-- An integral basis is determined by its generator. Source: the cyclic
local homology description in Hatcher, Section 3.3, p. 234. -/
theorem basis_apply (O : LocalOrientation X) (x : X) (z : Int) :
    O.basis x z = z • O.atPoint x := by
  simpa using map_zsmul (O.basis x) z (1 : Int)

/-- No local orientation generator is zero. Source: Hatcher, p. 234. -/
theorem atPoint_ne_zero (O : LocalOrientation X) (x : X) : O.atPoint x ≠ 0 := by
  rw [← O.basis_one x, ← (O.basis x).map_zero]
  exact fun h => one_ne_zero ((O.basis x).injective h)

/-- A local orientation generator cannot equal its negative over the integers.
Source: Hatcher, Section 3.3, p. 235. -/
theorem atPoint_ne_neg (O : LocalOrientation X) (x : X) :
    O.atPoint x ≠ -O.atPoint x := by
  intro h
  have he : (1 : Int) = -1 := (O.basis x).injective (by
    simpa only [map_neg, basis_one] using h)
  omega

/-- Restriction of an orientation along a topological open embedding.
Source: Hatcher, Section 3.3, p. 234 and Exercise 3, p. 257. -/
def pullback [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O : LocalOrientation Y) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) :
    LocalOrientation X where
  atPoint := integralOpenOrientation f hf O.atPoint
  generates x := by
    refine ⟨(O.basis (f x)).trans (localHomologyEquiv f hf x 3).symm, ?_⟩
    apply (localHomologyEquiv f hf x 3).injective
    change (localHomologyEquiv f hf x 3)
      ((localHomologyEquiv f hf x 3).symm (O.basis (f x) 1)) = _
    rw [LinearEquiv.apply_symm_apply, basis_one]
    exact (localHomologyMap_openOrientation f hf O.atPoint x).symm
  locallyRepresented := integralOpenOrientation_locallyRepresented f hf
    O.atPoint O.locallyRepresented

/-- Pullback and the induced local homology map are inverse at each point.
Source: Hatcher, Section 3.3, p. 234. -/
theorem map_pullback [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O : LocalOrientation Y) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (x : X) :
    localHomologyMap f hf.injective x 3 ((O.pullback f hf).atPoint x) =
      O.atPoint (f x) :=
  localHomologyMap_openOrientation f hf O.atPoint x

/-- The coefficient comparing two local orientations is locally constant.
Source: Hatcher, Section 3.3, pp. 234-235. -/
theorem comparison_locallyConstant [T2Space X] (O P : LocalOrientation X) :
    IsLocallyConstant (fun x : X => (P.basis x).symm (O.atPoint x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  let z : Int := (P.basis x).symm (O.atPoint x)
  obtain ⟨U, hU, hxU, a, ha⟩ := O.locallyRepresented x
  obtain ⟨V, hV, hxV, b, hb⟩ := P.locallyRepresented x
  have hpoint : integralSupportHomologyRestriction (singleton_subset_iff.mpr hxU) 3 a =
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hxV) 3 (z • b) := by
    rw [map_zsmul, ha x hxU, hb x hxV, ← P.basis_apply,
      LinearEquiv.apply_symm_apply]
  obtain ⟨W, hW, hxW, he⟩ :=
    exists_open_integralSupportHomology_restrictions_eq U V 3 a (z • b) x hxU hxV hpoint
  refine ⟨U ∩ V ∩ W, (hU.inter hV).inter hW, ⟨⟨hxU, hxV⟩, hxW⟩, ?_⟩
  intro y hy
  apply (P.basis y).injective
  rw [LinearEquiv.apply_symm_apply, P.basis_apply]
  have h := he y hy
  simpa only [map_zsmul, ha y hy.1.1, hb y hy.1.2] using h

/-- On a connected space, agreement at one point determines an orientation.
Source: Hatcher, Proposition 3.25 and its proof, pp. 234-235. -/
theorem atPoint_eq_of_eq [T2Space X] [PreconnectedSpace X]
    (O P : LocalOrientation X) (x : X) (hx : O.atPoint x = P.atPoint x) (y : X) :
    O.atPoint y = P.atPoint y := by
  have h := (O.comparison_locallyConstant P).apply_eq_of_preconnectedSpace y x
  have hx' : (P.basis x).symm (O.atPoint x) = 1 := by
    rw [hx, ← P.basis_one x, LinearEquiv.symm_apply_apply]
  rw [hx'] at h
  have he := congrArg (P.basis y) h
  simpa only [LinearEquiv.apply_symm_apply, basis_one] using he

end LocalOrientation

end Poincare.Topology.Orientation.ProjectivePlane
