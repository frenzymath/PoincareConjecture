import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Homology.Local
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set Filter
open scoped Topology

universe u

namespace Poincare.Topology.Orientation.ProjectivePlane

open Poincare.Topology

structure LocalOrientation (X : Type u) [TopologicalSpace X] where

  atPoint : ∀ x : X, LocalHomology X x 3

  generates : ∀ x : X, ∃ e : Int ≃ₗ[Int] LocalHomology X x 3, e 1 = atPoint x

  locallyRepresented : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3, ∀ y : X, ∀ hy : y ∈ U,
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = atPoint y

namespace LocalOrientation

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

def basis (O : LocalOrientation X) (x : X) : Int ≃ₗ[Int] LocalHomology X x 3 :=
  (O.generates x).choose

@[simp]
theorem basis_one (O : LocalOrientation X) (x : X) : O.basis x 1 = O.atPoint x :=
  (O.generates x).choose_spec

theorem basis_apply (O : LocalOrientation X) (x : X) (z : Int) :
    O.basis x z = z • O.atPoint x := by
  simpa using map_zsmul (O.basis x) z (1 : Int)

theorem atPoint_ne_zero (O : LocalOrientation X) (x : X) : O.atPoint x ≠ 0 := by
  rw [← O.basis_one x, ← (O.basis x).map_zero]
  exact fun h => one_ne_zero ((O.basis x).injective h)

theorem atPoint_ne_neg (O : LocalOrientation X) (x : X) :
    O.atPoint x ≠ -O.atPoint x := by
  intro h
  have he : (1 : Int) = -1 := (O.basis x).injective (by
    simpa only [map_neg, basis_one] using h)
  omega

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

theorem map_pullback [T2Space X] [T2Space Y] [LocallyCompactSpace X]
    (O : LocalOrientation Y) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (x : X) :
    localHomologyMap f hf.injective x 3 ((O.pullback f hf).atPoint x) =
      O.atPoint (f x) :=
  localHomologyMap_openOrientation f hf O.atPoint x

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
