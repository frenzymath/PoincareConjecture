import PoincareConjecture.Proofs.M76.Wall.ProtectedRegionHomotopies
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1



theorem exists_prescribed_frontier_filling_in_protected_region
    {X : Type*} [TopologicalSpace X] {R C F : Set X}
    (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C)
    (gamma : C(Q, F)) :
    ∃ f : C(D, (R \ C : Set X)),
      ∀ x : Q, (f ⟨x, sphere_subset_closedBall x.property⟩ : X) = (gamma x : X) := by
  let rim : C(Q, (R \ C : Set X)) := (ContinuousMap.inclusion hFU).comp gamma
  have hcontract : (Dehn.squareRimLoop.map rim.continuous).Homotopic
      (Path.refl (rim Dehn.squareRimBase)) :=
    exists_frontier_loop_homotopy_in_protected_region hloops
      (rim Dehn.squareRimBase) (Dehn.squareRimLoop.map rim.continuous)
      (fun t => (gamma (Dehn.squareRimLoop t)).property)
  have hnull : rim.Nullhomotopic := Dehn.nullhomotopic_of_squareRimLoop rim hcontract
  obtain ⟨f, hf⟩ := hnull.exists_closedBall_extension rim
  exact ⟨f, fun x => congrArg (Subtype.val : (R \ C : Set X) → X) (hf x)⟩

end PoincareConjecture.M76
