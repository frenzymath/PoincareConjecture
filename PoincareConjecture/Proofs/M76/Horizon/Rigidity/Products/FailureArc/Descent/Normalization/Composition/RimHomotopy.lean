import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Homotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PreservedMarkHomotopy
import Mathlib.Topology.Homotopy.Contractible









set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem FiniteMarkedSurfaceRepairs.exists_original_marked_rim_homotopy
    {s t : Stage e S f r C} {step : Step s t} {R : Set M}
    {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    (F : Bool → Set M) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    {D : MarkedSurfacePositionData step K₀ A₀ j R (F false ∪ F true)}
    (repairs : FiniteMarkedSurfaceRepairs D)
    {Y : Type*} [TopologicalSpace Y] (b : Bool) (u : C(Y, A₀.space))
    (gamma : C(Y, F b))
    (hgamma : ∀ y, (gamma y : M) = t.projection (j (u y))) :
    ∃ (gamma' : C(Y, F b)) (_eta : gamma.Homotopy gamma'),
      ∀ y, (gamma' y : M) = t.projection (repairs.composite 1 (D.endpoint (u y))) := by
  obtain ⟨G, hG, _, hzero, hsets, hfinal⟩ := repairs.exists_ambient_history
  have hAK : A₀.space ⊆ D.K.space :=
    D.boundary_space.symm.subset.trans
      (SimplicialComplex.space_subset_of_le D.boundary_subcomplex)
  have hjcont : Continuous (fun y : Y => j (u y)) := by
    have hh := ((D.states 0).original_PL.continuousOn.mono hAK).domRestrict.comp u.continuous
    change Continuous ((A₀.space.domRestrict j) ∘ u)
    simpa only [D.first_state] using hh
  obtain ⟨gamma', eta, hvalue, _⟩ :=
    PoincareConjecture.M76.exists_parametrized_homotopy_in_preserved_mark t.projection R F
      hF hopen hdis G hG hzero (fun a => (hsets a).2) b
      ⟨fun y => j (u y), hjcont⟩ gamma hgamma
  refine ⟨gamma', eta, ?_⟩
  intro y
  exact (hvalue y).trans (congrArg t.projection (congrFun hfinal (u y)).symm)

theorem FiniteMarkedSurfaceRepairs.exists_original_essential_marked_rim
    {s t : Stage e S f r C} {step : Step s t} {R : Set M}
    {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    (F : Bool → Set M) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    {D : MarkedSurfacePositionData step K₀ A₀ j R (F false ∪ F true)}
    (repairs : FiniteMarkedSurfaceRepairs D)
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (b : Bool) (u : C(Y, A₀.space)) (gamma : C(Y, F b))
    (hgamma : ∀ y, (gamma y : M) = t.projection (j (u y)))
    (projection : C(F b, Z)) (hessential : ¬ (projection.comp gamma).Nullhomotopic) :
    ∃ (gamma' : C(Y, F b)) (_eta : gamma.Homotopy gamma'),
      (∀ y, (gamma' y : M) = t.projection (repairs.composite 1 (D.endpoint (u y)))) ∧
      ¬ (projection.comp gamma').Nullhomotopic := by
  obtain ⟨gamma', eta, hvalue⟩ :=
    repairs.exists_original_marked_rim_homotopy F hF hopen hdis b u gamma hgamma
  refine ⟨gamma', eta, hvalue, ?_⟩
  rintro ⟨z, hz⟩
  apply hessential
  exact ⟨z, (ContinuousMap.Homotopic.comp (.refl projection) ⟨eta⟩).trans hz⟩

end Geometry.OriginalPLTower
