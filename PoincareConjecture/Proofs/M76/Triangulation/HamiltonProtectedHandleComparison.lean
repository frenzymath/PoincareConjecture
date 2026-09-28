import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardIrreducibility
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainComposition
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedCompression
import PoincareConjecture.Proofs.M76.Triangulation.BoundedHandleLift











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
  {α β : Type*}

local notation "V3" => (Fin 3 → ℝ)
local notation "X" => LatticeHandleAmbient ι κ L
local notation "R" => latticeHandleDomain ι κ L
local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)
local notation "D" => coordinateCylinder J





theorem exists_hamilton_protected_handle_comparison
    (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hindex : Fintype.card ι + Fintype.card κ = 3) (hlower : Fintype.card ι ≤ 2)
    (he : PLDomain e R) (hd : StandardLatticeHandleAtlas ι κ L d)
    (prime : HasHamiltonProtectedIrreducibleReplacement ι κ L e)
    (approximation : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasRelativeBoundaryProperPLApproximation
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d R)
    (rigidity : ∀ charts : Set (OpenPartialHomeomorph X V3),
      HasHamiltonRelativeTorusRigidity ι κ L
        (fun c : charts => (c : OpenPartialHomeomorph X V3)) d)
    (P : Set X) (hP : Nonempty (HamiltonMarkedProtectedBall ι κ L e P))
    (U : Set R) (hBU : (Subtype.val : R → X) ⁻¹' frontier R ⊆ U)
    (hboundary : ChartwisePLOn e d (ContinuousMap.id R) U)
    {r : ℝ} (hr : 1 < r) (hr2 : r < 2) :
    ∃ (charts : Set (OpenPartialHomeomorph X V3)) (N : Set X),
      IsOpen N ∧ P ∪ frontier R ⊆ N ∧
      IsPLIrreducible (fun c : charts => (c : OpenPartialHomeomorph X V3)) R ∧
      ChartwisePLOn e (fun c : charts => (c : OpenPartialHomeomorph X V3))
        (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' N) ∧
      ChartwisePLOn (fun c : charts => (c : OpenPartialHomeomorph X V3)) e
        (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' N) ∧
      ∃ g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L,
        ChartwisePLHomeomorph (fun c : charts => (c : OpenPartialHomeomorph X V3)) d
          (latticeHandleHomeomorphInDomain ι κ L g) ∧
        ∃ G : D ≃ₜ D,
          (∀ x, ((coordinateCylinderProduct ι κ (G x)).1,
              QuotientAddGroup.mk (coordinateCylinderProduct ι κ (G x)).2) =
            g ((coordinateCylinderProduct ι κ x).1,
              QuotientAddGroup.mk (coordinateCylinderProduct ι κ x).2)) ∧
          (∀ x : D, (x : V) ∈ frontier D → G x = x) ∧
          ∃ bound > 0, (∀ x : D, ‖(G x : V) - x‖ ≤ bound) ∧
            ∃ p : OpenPartialHomeomorph V V,
              p.source = univ ∧ p.target = ball 0 2 ∧
              (∀ x, ‖x‖ ≤ 1 → p x = x) ∧
              (∀ x ∈ D, ‖x‖ ≤ r → p x = x) ∧
              LocallyPiecewiseAffineOn p p.source ∧
              LocallyPiecewiseAffineOn p.symm p.target ∧
              ∃ A : V ≃ₜ V,
                (∀ x : D, A (p x) = p (G x)) ∧
                Nonempty (ContinuousMap.HomotopyWith (ContinuousMap.id V) ⟨A, A.continuous⟩
                  (fun f => IsHomeomorph f ∧ (∀ x, 2 ≤ ‖x‖ → f x = x) ∧
                    ∀ x ∈ Dᶜ ∪ frontier D, f x = x)) := by
  obtain ⟨charts, N, hN, hPN, hirr, hee', he'e⟩ :=
    prime hindex hlower inferInstance he P hP
  let e' := fun c : charts => (c : OpenPartialHomeomorph X V3)
  let W : Set R := (Subtype.val : R → X) ⁻¹' N ∩ U
  have hW : ChartwisePLOn e' d (ContinuousMap.id R) W := by
    simpa only [ContinuousMap.comp_id, ContinuousMap.coe_id, preimage_id_eq, id_eq, e', W] using
      hboundary.comp he'e
  have hBW : (Subtype.val : R → X) ⁻¹' frontier R ⊆ W := by
    intro x hx
    exact ⟨hPN (Or.inr hx), hBU hx⟩
  obtain ⟨phi, hphi, hproper, hidentity⟩ :=
    exists_hamilton_marked_relative_approximation ι κ L e' d (approximation charts)
      hirr.1 hd W hW.open_domain hBW hW
  obtain ⟨g, hgPL, _, ⟨Hg⟩⟩ :=
    rigidity charts hindex hlower hd hirr (hd.isPLIrreducible ι κ L hindex)
      phi hphi hproper hidentity
  obtain ⟨G, hG, hGfront, bound, hbound, hGbound⟩ :=
    exists_boundedHandleLift ι κ L g Hg
  obtain ⟨p, hps, hpt, hpcore, hpwide, hpPL, hpiPL, hcompact⟩ :=
    exists_plHandleCompactification_with_protected_core (ι ⊕ κ) J hr hr2
  obtain ⟨A, hA, hhomotopy⟩ := hcompact G bound hbound.le hGbound hGfront
  exact ⟨charts, N, hN, hPN, hirr, hee', he'e, g, hgPL, G, hG, hGfront,
    bound, hbound, hGbound, p, hps, hpt, hpcore, hpwide, hpPL, hpiPL, A, hA, hhomotopy⟩

end PoincareConjecture.M76
