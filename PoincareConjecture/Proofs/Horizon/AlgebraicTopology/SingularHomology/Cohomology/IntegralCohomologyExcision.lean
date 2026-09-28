import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralRelativeFree
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCochains
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralExcision
import Mathlib.Algebra.Homology.DerivedCategory.KProjective









set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set

universe u

namespace Poincare.Topology

theorem integralDualMap_quasiIso_of_projective
    {C D : ChainComplex (ModuleCat.{u} Int) Nat}
    [∀ n, CategoryTheory.Projective (C.X n)]
    [∀ n, CategoryTheory.Projective (D.X n)]
    (f : C ⟶ D) (hf : QuasiIso f) : QuasiIso (integralDualMap f) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp hf
  rw [← he]
  exact (integralDualHomotopyEquiv e).quasiIso_hom

theorem integralRelative_dual_quasiIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y)
    (f : integralRelativeChains A ⟶ integralRelativeChains B) (hf : QuasiIso f) :
    QuasiIso (integralDualMap f) := by
  let : ∀ n, CategoryTheory.Projective ((integralRelativeChains A).X n) :=
    integralRelativeChains_projective A
  let : ∀ n, CategoryTheory.Projective ((integralRelativeChains B).X n) :=
    integralRelativeChains_projective B
  exact integralDualMap_quasiIso_of_projective f hf

theorem integral_open_cover_cohomology_excision
    {X : Type u} [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) (n : Nat) :
    IsIso (homologyMap
      (integralDualMap
        (integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
          (A := (Subtype.val : B → X) ⁻¹' A) (B := A) (fun _ hb => hb))) n) := by
  let f := integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
    (A := (Subtype.val : B → X) ⁻¹' A) (B := A) (fun _ hb => hb)
  have hf : QuasiIso f := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact integral_open_cover_excision A B hA hB hcover i
  let : QuasiIso (integralDualMap f) := integralRelative_dual_quasiIso _ _ f hf
  change IsIso (homologyMap (integralDualMap f) n)
  infer_instance

end Poincare.Topology
