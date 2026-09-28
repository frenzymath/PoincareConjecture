import PoincareConjecture.Proofs.M02.Topology.IntegralManifoldOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactGluing
import Mathlib.Topology.Sets.Compacts

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]

variable (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
  (omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
  (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y)

def integralCompactSupportOrientation
    (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (K : Compacts X)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U 3,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y) :
    integralSupportHomology (K : Set X) 3 :=
  Classical.choose (exists_unique_integralSupportHomology_compact_gluing
    3 hD omega (K : Set X) (by exact K.isCompact) (fun x _ => hlocal x))

theorem integralCompactSupportOrientation_spec
    (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (K : Compacts X)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U 3,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y) :
    ∀ x : X, ∀ hx : x ∈ (K : Set X),
      integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3
          (integralCompactSupportOrientation hD omega K hlocal) = omega x :=
  (Classical.choose_spec (exists_unique_integralSupportHomology_compact_gluing
    3 hD omega (K : Set X) (by exact K.isCompact) (fun x _ => hlocal x))).1

theorem integralCompactSupportOrientation_restrict
    (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
    (omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ b : integralSupportHomology U 3,
        ∀ y : X, ∀ hy : y ∈ U,
          integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y)
    {K L : Compacts X} (hKL : K ≤ L) :
    integralSupportHomologyRestriction (show (K : Set X) ⊆ (L : Set X) from hKL) 3
        (integralCompactSupportOrientation hD omega L hlocal) =
      integralCompactSupportOrientation hD omega K hlocal := by
  apply sub_eq_zero.mp
  apply hD (K : Set X) K.isCompact
  intro x hx
  rw [map_sub]
  have hL := integralCompactSupportOrientation_spec hD omega L hlocal x (hKL hx)
  have hK := integralCompactSupportOrientation_spec hD omega K hlocal x hx
  have hcomp := integralSupportHomologyRestriction_comp
    (singleton_subset_iff.mpr hx)
    (show (K : Set X) ⊆ (L : Set X) from fun y hy => hKL hy) 3
  let hKLset : (K : Set X) ⊆ (L : Set X) := fun y hy => hKL hy
  have hL' :
      (integralSupportHomologyRestriction (singleton_subset_iff.mpr hx) 3)
          ((integralSupportHomologyRestriction hKLset 3)
            (integralCompactSupportOrientation hD omega L hlocal)) = omega x := by
    have hc := congrArg
      (fun q => q (integralCompactSupportOrientation hD omega L hlocal)) hcomp
    exact hc.trans hL
  rw [hL', hK, sub_self]

end PoincareConjecture.Proofs.M02.Topology
