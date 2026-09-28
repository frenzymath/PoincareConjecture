import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Orientation.IntegralCompactOrientation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Duality.CapProduct.IntegralSupportCapNaturality
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomology







set_option autoImplicit false

noncomputable section

open CategoryTheory TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [RegularSpace X]

variable (hD : ∀ L : Set X, IsCompact L → IntegralSupportDetected L 3)
  (omega : ∀ x : X, integralSupportHomology ({x} : Set X) 3)
  (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ b : integralSupportHomology U 3,
      ∀ y : X, ∀ hy : y ∈ U,
        integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y)

private def compactCapOne (K : Compacts X) :
    integralSupportCohomology (K : Set X) 1 ⟶ integralHomology X 2 :=
  ModuleCat.ofHom (integralSupportCapHomologyOne (K : Set X)ᶜ
    (integralCompactSupportOrientation hD omega K hlocal))

private def compactCapTwo (K : Compacts X) :
    integralSupportCohomology (K : Set X) 2 ⟶ integralHomology X 1 :=
  ModuleCat.ofHom (integralSupportCapHomologyTwo (K : Set X)ᶜ
    (integralCompactSupportOrientation hD omega K hlocal))

private def compactCapThree (K : Compacts X) :
    integralSupportCohomology (K : Set X) 3 ⟶ integralHomology X 0 :=
  ModuleCat.ofHom (integralSupportCapHomologyThree (K : Set X)ᶜ
    (integralCompactSupportOrientation hD omega K hlocal))

private theorem compactCapOne_compatible {K L : Compacts X} (hKL : K ≤ L) :
    integralSupportCohomologyPushforward (show (K : Set X) ⊆ (L : Set X) from fun x hx =>
      @hKL x hx) 1 ≫ compactCapOne hD omega hlocal L =
      compactCapOne hD omega hlocal K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change integralSupportCapHomologyOne (L : Set X)ᶜ
      (integralCompactSupportOrientation hD omega L hlocal)
        (integralSupportCohomologyPushforward hKL 1 phi) =
    integralSupportCapHomologyOne (K : Set X)ᶜ
      (integralCompactSupportOrientation hD omega K hlocal) phi
  rw [integralSupportCapHomologyOne_naturality (fun x hx => hKL hx)]
  rw [integralCompactSupportOrientation_restrict hD omega hlocal hKL]

private theorem compactCapTwo_compatible {K L : Compacts X} (hKL : K ≤ L) :
    integralSupportCohomologyPushforward (show (K : Set X) ⊆ (L : Set X) from fun x hx =>
      @hKL x hx) 2 ≫ compactCapTwo hD omega hlocal L =
      compactCapTwo hD omega hlocal K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change integralSupportCapHomologyTwo (L : Set X)ᶜ
      (integralCompactSupportOrientation hD omega L hlocal)
        (integralSupportCohomologyPushforward hKL 2 phi) =
    integralSupportCapHomologyTwo (K : Set X)ᶜ
      (integralCompactSupportOrientation hD omega K hlocal) phi
  rw [integralSupportCapHomologyTwo_naturality (fun x hx => hKL hx)]
  rw [integralCompactSupportOrientation_restrict hD omega hlocal hKL]

private theorem compactCapThree_compatible {K L : Compacts X} (hKL : K ≤ L) :
    integralSupportCohomologyPushforward (show (K : Set X) ⊆ (L : Set X) from fun x hx =>
      @hKL x hx) 3 ≫ compactCapThree hD omega hlocal L =
      compactCapThree hD omega hlocal K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro phi
  change integralSupportCapHomologyThree (L : Set X)ᶜ
      (integralCompactSupportOrientation hD omega L hlocal)
        (integralSupportCohomologyPushforward hKL 3 phi) =
    integralSupportCapHomologyThree (K : Set X)ᶜ
      (integralCompactSupportOrientation hD omega K hlocal) phi
  rw [integralSupportCapHomologyThree_naturality (fun x hx => hKL hx)]
  rw [integralCompactSupportOrientation_restrict hD omega hlocal hKL]

def integralCompactSupportCapOne :
    integralCompactSupportCohomology X 1 ⟶ integralHomology X 2 :=
  integralCompactSupportCohomologyDesc 1 (integralHomology X 2)
    (compactCapOne hD omega hlocal)
    (fun K L hKL => compactCapOne_compatible hD omega hlocal (K := K) (L := L) hKL)

def integralCompactSupportCapTwo :
    integralCompactSupportCohomology X 2 ⟶ integralHomology X 1 :=
  integralCompactSupportCohomologyDesc 2 (integralHomology X 1)
    (compactCapTwo hD omega hlocal)
    (fun K L hKL => compactCapTwo_compatible hD omega hlocal (K := K) (L := L) hKL)

def integralCompactSupportCapThree :
    integralCompactSupportCohomology X 3 ⟶ integralHomology X 0 :=
  integralCompactSupportCohomologyDesc 3 (integralHomology X 0)
    (compactCapThree hD omega hlocal)
    (fun K L hKL => compactCapThree_compatible hD omega hlocal (K := K) (L := L) hKL)

@[reassoc (attr := simp)]
theorem integralCompactSupportCapOne_class (K : Compacts X) :
    integralCompactSupportCohomologyClass K 1 ≫
        integralCompactSupportCapOne hD omega hlocal =
      compactCapOne hD omega hlocal K :=
  integralCompactSupportCohomologyClass_desc 1 (integralHomology X 2)
    (compactCapOne hD omega hlocal)
    (fun K L hKL => compactCapOne_compatible hD omega hlocal (K := K) (L := L) hKL) K

@[reassoc (attr := simp)]
theorem integralCompactSupportCapTwo_class (K : Compacts X) :
    integralCompactSupportCohomologyClass K 2 ≫
        integralCompactSupportCapTwo hD omega hlocal =
      compactCapTwo hD omega hlocal K :=
  integralCompactSupportCohomologyClass_desc 2 (integralHomology X 1)
    (compactCapTwo hD omega hlocal)
    (fun K L hKL => compactCapTwo_compatible hD omega hlocal (K := K) (L := L) hKL) K

@[reassoc (attr := simp)]
theorem integralCompactSupportCapThree_class (K : Compacts X) :
    integralCompactSupportCohomologyClass K 3 ≫
        integralCompactSupportCapThree hD omega hlocal =
      compactCapThree hD omega hlocal K :=
  integralCompactSupportCohomologyClass_desc 3 (integralHomology X 0)
    (compactCapThree hD omega hlocal)
    (fun K L hKL => compactCapThree_compatible hD omega hlocal (K := K) (L := L) hKL) K

end Poincare.Topology
