import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false

universe u v w z

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {ι : Type w} {κ : Type z} {R : Set X} {T : Set Y}

structure ChartwisePLOn (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph Y V3) (f : C(R, T)) (U : Set R) : Prop where
  source_domain : PLDomain e R
  target_domain : PLDomain d T
  open_domain : IsOpen U
  coordinates : ∀ x : R, x ∈ U →
    ∃ (i : ι) (j : κ) (K : SimplicialComplex ℝ V3) (V : Set R) (F : V3 → V3),
      K.faces.Finite ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      MapsTo (Subtype.val : R → X) V (e i).source ∧
      ((e i) ∘ (Subtype.val : R → X)) '' V ⊆ K.space ∧
      K.space ⊆ (e i).target ∧
      MapsTo (e i).symm K.space ((Subtype.val : R → X) '' U) ∧
      FinitePiecewiseAffineOn F K.space ∧
      ∀ y : R, (y : X) ∈ (e i).source → e i y ∈ K.space →
        (f y : Y) ∈ (d j).source ∧ F (e i y) = d j (f y)

def ChartwisePLMap (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph Y V3) (f : C(R, T)) : Prop :=
  ChartwisePLOn e d f univ

def ChartwisePLHomeomorph (e : ι → OpenPartialHomeomorph X V3)
    (d : κ → OpenPartialHomeomorph Y V3) (h : R ≃ₜ T) : Prop :=
  ChartwisePLMap e d ⟨h, h.continuous⟩ ∧
    ChartwisePLMap d e ⟨h.symm, h.symm.continuous⟩

end PoincareConjecture.M76
