import PoincareConjecture.Proofs.M83.Mathlib.LocalHomology
import PoincareConjecture.Proofs.M02.Topology.PositiveLinearHomotopy

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Set

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

theorem positiveLinear_relativeHomologyMap
    (L : EuclideanSpace Real (Fin 3) ≃L[Real] EuclideanSpace Real (Fin 3))
    (hL : 0 < L.toLinearEquiv.toLinearMap.det) (d : Nat) :
    homologyMap (integralRelativeMap (⟨L, L.continuous⟩ :
      C(EuclideanSpace Real (Fin 3), EuclideanSpace Real (Fin 3)))
      (A := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
      (B := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
      (by intro x hx h; exact hx (L.injective (h.trans L.map_zero.symm)))) d =
        𝟙 (LocalHomology (EuclideanSpace Real (Fin 3)) 0 d) := by
  obtain ⟨H, hH⟩ := exists_positive_linear_puncture_homotopy L hL
  have h := relativeHomologyMap_eq_of_homotopy H
    (A := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
    (B := ({0}ᶜ : Set (EuclideanSpace Real (Fin 3))))
    (fun _ hx => hx)
    (by intro x hx h; exact hx (L.injective (h.trans L.map_zero.symm))) hH d
  rw [← h]
  exact localHomologyMap_id 0 d

end PoincareConjecture.Proofs.M83
