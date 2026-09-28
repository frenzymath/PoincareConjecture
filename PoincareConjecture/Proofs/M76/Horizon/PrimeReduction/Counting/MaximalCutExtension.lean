import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCutExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_punctured_extension_with_original_collar
    {X : Type*} {κ : Type u} {ι E : Type*} [MetricSpace X] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X} (f : X → E)
    (c : MarkedSphereCut e R κ)
    (hmax : ∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card ν ≤ Fintype.card κ)
    (sT : ChartwisePLSphere e T) (hT : T ⊆ interior c.carrier)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (d : MarkedSphereCut e R (Option κ)) (x : X),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier ∧
      x ∈ d.carrier ∧ HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) ∧
      Nonempty (OriginalFiniteSphereCollar e c.carrier T (d.collar none)
        (fun b => d.ports (none,b))) ∧
      ∀ (b : Bool) (A : Set X), ChartwisePLBall e A (d.ports (none,b)) → A ⊆ d.carrier →
        ∃ A' : Set X, Nonempty (ChartwisePLBall e A' T) ∧ A ⊆ interior A' ∧
          A' ⊆ A ∪ closure (d.collar none) ∧ A' ⊆ c.carrier := by
  classical
  obtain ⟨d,hS,hO,hB,hcarrier,hclosed,hraw,htransfer⟩ :=
    c.exists_extension_with_original_collar sT hT hU hTU
  have hnot : ¬ HasNoPuncturedSphereComponents e f d.carrier := by
    intro hd
    have h := hmax (Option κ) d hd
    simp only [Fintype.card_option] at h
    omega
  simp only [HasNoPuncturedSphereComponents,not_forall,not_not] at hnot
  obtain ⟨x,hx,hmodel⟩ := hnot
  exact ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel,hraw,htransfer⟩

theorem MarkedSphereCut.exists_punctured_extension_with_endpoint_transfer
    {X : Type*} {κ : Type u} {ι E : Type*} [MetricSpace X] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X} (f : X → E)
    (c : MarkedSphereCut e R κ)
    (hmax : ∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card ν ≤ Fintype.card κ)
    (sT : ChartwisePLSphere e T) (hT : T ⊆ interior c.carrier)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (d : MarkedSphereCut e R (Option κ)) (x : X),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier ∧
      x ∈ d.carrier ∧ HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) ∧
      ∀ (b : Bool) (A : Set X), ChartwisePLBall e A (d.ports (none,b)) → A ⊆ d.carrier →
        ∃ A' : Set X, Nonempty (ChartwisePLBall e A' T) ∧ A ⊆ interior A' ∧
          A' ⊆ A ∪ closure (d.collar none) ∧ A' ⊆ c.carrier := by
  obtain ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel,_,htransfer⟩ :=
    c.exists_punctured_extension_with_original_collar f hmax sT hT hU hTU
  exact ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel,htransfer⟩

theorem MarkedSphereCut.exists_punctured_extension
    {X : Type*} {κ : Type u} {ι E : Type*} [MetricSpace X] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R T U : Set X} (f : X → E)
    (c : MarkedSphereCut e R κ)
    (hmax : ∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card ν ≤ Fintype.card κ)
    (sT : ChartwisePLSphere e T) (hT : T ⊆ interior c.carrier)
    (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (d : MarkedSphereCut e R (Option κ)) (x : X),
      d.spheres = (fun i : Option κ => i.elim T c.spheres) ∧
      (∀ i,d.collar (some i) = c.collar i) ∧
      (∀ i b,d.ports (some i,b) = c.ports (i,b)) ∧
      d.carrier = c.carrier \ d.collar none ∧
      closure (d.collar none) ⊆ U ∩ interior c.carrier ∧
      x ∈ d.carrier ∧ HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) := by
  obtain ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel,_⟩ :=
    c.exists_punctured_extension_with_endpoint_transfer f hmax sT hT hU hTU
  exact ⟨d,x,hS,hO,hB,hcarrier,hclosed,hx,hmodel⟩

end PoincareConjecture.M76
