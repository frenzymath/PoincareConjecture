import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Collars.ProtectedFrontierBicollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.SquareRimFilling
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ContractibleBallExtension

/-!
# Same-side fillings in a protected frontier bicollar

An actual loop in one open side of a protected bicollar is filled by filling
its frontier projection and its signed depth coordinate independently. The
resulting disk remains in that same side and has the literal original loop as
its boundary. See Wall005, step 4, and Hatcher, Corollary 3.3, p. 48.
-/

set_option autoImplicit false

open Set Metric Geometry unitInterval BrownCollar

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- Fill a concrete loop represented in the positive side of the previously
constructed protected bicollar when its frontier projection is null. The
disk is constructed from the two exact coordinate extensions. -/
theorem PLDomain.exists_same_side_bicollar_filling
    {X : Type*} [TopologicalSpace X] {K Y F : Set X}
    (hcut : Y ∩ frontier K = F)
    (G : (F × Ioo (-1 : ℝ) 1) ≃ₜ Y)
    (hside : ∀ z, (G z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ))
    (hzero : ∀ z, (G z : X) ∈ F ↔ (z.2 : ℝ) = 0)
    (beta : C(Q, F)) (depth : C(Q, Ioo (0 : ℝ) 1))
    (hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map beta.continuous)) = 1) :
    ∃ (eta : C(Q, Y)) (fill : C(D, Y)),
      (∀ u, eta u = G (beta u, ⟨depth u, by
        constructor <;> linarith [(depth u).property.1, (depth u).property.2]⟩)) ∧
      (∀ u : Q, fill ⟨u, sphere_subset_closedBall u.property⟩ = eta u) ∧
      (∀ x : D, (fill x : X) ∈ interior K) ∧
      (∀ x : D, (fill x : X) ∉ F) := by
  have hcontract : (Dehn.squareRimLoop.map beta.continuous).Homotopic
      (Path.refl (beta Dehn.squareRimBase)) := Path.Homotopic.Quotient.exact hnull
  obtain ⟨baseFill, hbaseFill⟩ :=
    (Dehn.nullhomotopic_of_squareRimLoop beta hcontract).exists_closedBall_extension beta
  let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨depthFill, hdepthFill⟩ :=
    ContinuousMap.exists_closedBall_extension_of_contractible depth
  let pos : C(Ioo (0 : ℝ) 1, Ioo (-1 : ℝ) 1) :=
    ⟨fun r => ⟨r, by constructor <;> linarith [r.property.1, r.property.2]⟩, by fun_prop⟩
  let eta : C(Q, Y) :=
    ⟨fun u => G (beta u, pos (depth u)), G.continuous.comp
      (beta.continuous.prodMk (pos.continuous.comp depth.continuous))⟩
  let fill : C(D, Y) :=
    ⟨fun x => G (baseFill x, pos (depthFill x)), G.continuous.comp
      (baseFill.continuous.prodMk (pos.continuous.comp depthFill.continuous))⟩
  refine ⟨eta, fill, fun u => rfl, ?_, ?_, ?_⟩
  · intro u
    change G (baseFill ⟨u, sphere_subset_closedBall u.property⟩,
      pos (depthFill ⟨u, sphere_subset_closedBall u.property⟩)) = G (beta u, pos (depth u))
    rw [hbaseFill, hdepthFill]
  · intro x
    exact (mem_interior_iff_notMem_frontier ((hside (baseFill x, pos (depthFill x))).mpr
      (le_of_lt (depthFill x).property.1))).mpr (by
      intro hx
      exact (ne_of_gt (depthFill x).property.1)
        ((hzero (baseFill x, pos (depthFill x))).mp (hcut.subset ⟨(fill x).property, hx⟩)))
  · intro x hx
    exact (ne_of_gt (depthFill x).property.1)
      ((hzero (baseFill x, pos (depthFill x))).mp hx)

/-- Negative-side counterpart of `exists_same_side_bicollar_filling`. -/
theorem PLDomain.exists_negative_side_bicollar_filling
    {X : Type*} [TopologicalSpace X] {K Y F : Set X}
    (G : (F × Ioo (-1 : ℝ) 1) ≃ₜ Y)
    (hside : ∀ z, (G z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ))
    (hzero : ∀ z, (G z : X) ∈ F ↔ (z.2 : ℝ) = 0)
    (beta : C(Q, F)) (depth : C(Q, Ioo (-1 : ℝ) 0))
    (hnull : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map beta.continuous)) = 1) :
    ∃ (eta : C(Q, Y)) (fill : C(D, Y)),
      (∀ u, eta u = G (beta u, ⟨depth u, by
        constructor <;> linarith [(depth u).property.1, (depth u).property.2]⟩)) ∧
      (∀ u : Q, fill ⟨u, sphere_subset_closedBall u.property⟩ = eta u) ∧
      (∀ x : D, (fill x : X) ∈ Kᶜ) ∧
      (∀ x : D, (fill x : X) ∉ F) := by
  have hcontract : (Dehn.squareRimLoop.map beta.continuous).Homotopic
      (Path.refl (beta Dehn.squareRimBase)) := Path.Homotopic.Quotient.exact hnull
  obtain ⟨baseFill, hbaseFill⟩ :=
    (Dehn.nullhomotopic_of_squareRimLoop beta hcontract).exists_closedBall_extension beta
  let : ContractibleSpace (Ioo (-1 : ℝ) 0) :=
    (convex_Ioo (-1 : ℝ) 0).contractibleSpace ⟨-1 / 2, by constructor <;> norm_num⟩
  obtain ⟨depthFill, hdepthFill⟩ :=
    ContinuousMap.exists_closedBall_extension_of_contractible depth
  let neg : C(Ioo (-1 : ℝ) 0, Ioo (-1 : ℝ) 1) :=
    ⟨fun r => ⟨r, by constructor <;> linarith [r.property.1, r.property.2]⟩, by fun_prop⟩
  let eta : C(Q, Y) :=
    ⟨fun u => G (beta u, neg (depth u)), G.continuous.comp
      (beta.continuous.prodMk (neg.continuous.comp depth.continuous))⟩
  let fill : C(D, Y) :=
    ⟨fun x => G (baseFill x, neg (depthFill x)), G.continuous.comp
      (baseFill.continuous.prodMk (neg.continuous.comp depthFill.continuous))⟩
  refine ⟨eta, fill, fun u => rfl, ?_, ?_, ?_⟩
  · intro u
    change G (baseFill ⟨u, sphere_subset_closedBall u.property⟩,
      neg (depthFill ⟨u, sphere_subset_closedBall u.property⟩)) = G (beta u, neg (depth u))
    rw [hbaseFill, hdepthFill]
  · intro x
    exact fun hx => (not_le_of_gt (depthFill x).property.2)
      ((hside (baseFill x, neg (depthFill x))).mp hx)
  · intro x hx
    exact (ne_of_lt (depthFill x).property.2)
      ((hzero (baseFill x, neg (depthFill x))).mp hx)

end PoincareMT.M76
