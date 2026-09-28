import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedBlockFrontier
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.HomotopyLoopContractions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem OriginalDiskProduct.exists_essential_lateral_rim
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (rim : C(Q, F)) (hrim : ∀ u : Q, (rim u : X) = j u)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1)
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
    ∃ (capRim : C(Q, F)) (H : rim.Homotopy capRim),
      (∀ u : Q, (capRim u : X) = P.map (u, s)) ∧
      (∀ z : unitInterval × Q, (H z : X) = P.map (z.2, (z.1 : ℝ) * s)) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map capRim.continuous)) ≠ 1 := by
  have hPF := P.protected_frontier_iff hcut hsmall
  have hprod (z : unitInterval × Q) :
      ((z.2 : V2), (z.1 : ℝ) * s) ∈ D ×ˢ Icc (-1 : ℝ) 1 := by
    refine ⟨sphere_subset_closedBall z.2.property, ?_, ?_⟩ <;>
      nlinarith [z.1.property.1, z.1.property.2, hs.1, hs.2,
        mul_nonneg z.1.property.1 (sub_nonneg.mpr hs.2),
        mul_nonneg z.1.property.1 (sub_nonneg.mpr hs.1)]
  let sweep : C(unitInterval × Q, F) :=
    ⟨fun z => ⟨P.map (z.2, (z.1 : ℝ) * s),
      (hPF _ (hprod z)).mpr z.2.property⟩,
      (P.polyhedral.continuousOn.comp_continuous
        (by fun_prop) hprod).subtype_mk _⟩
  let capRim : C(Q, F) := sweep.comp ⟨fun u => (1, u), by fun_prop⟩
  have hcap (u : Q) : (capRim u : X) = P.map (u, s) := by
    change P.map (u, (1 : ℝ) * s) = _
    rw [one_mul]
  let H : rim.Homotopy capRim :=
    { toContinuousMap := sweep
      map_zero_left := by
        intro u
        apply Subtype.ext
        change P.map (u, (0 : ℝ) * s) = (rim u : X)
        rw [zero_mul, P.central u (sphere_subset_closedBall u.property), hrim]
      map_one_left := fun _ => rfl }
  refine ⟨capRim, H, hcap, fun _ => rfl, ?_⟩
  intro hnull
  apply hessential
  exact Path.Homotopic.Quotient.eq.mpr
    (H.map_loop_homotopic_refl Dehn.squareRimLoop (Path.Homotopic.Quotient.exact hnull))

end PoincareConjecture.M76
