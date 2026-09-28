import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ConvexCircleRelativeHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBicollar
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem isPreconnected_hamiltonDiskRim :
    IsPreconnected {x : D | ‖(x : V2)‖ = 1} := by
  have hdim : 1 < Module.finrank ℝ V2 := by simp
  have hrank : 1 < Module.rank ℝ V2 := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hdim
  have himage : (Subtype.val : D → V2) '' {x : D | ‖(x : V2)‖ = 1} =
      sphere (0 : V2) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr hy
    · intro hx
      exact ⟨⟨x, sphere_subset_closedBall hx⟩, mem_sphere_zero_iff_norm.mp hx, rfl⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  rw [himage]
  exact (isConnected_sphere hrank 0 zero_le_one).isPreconnected

theorem exists_hamiltonSolidTorus_identity_homotopy
    (f : C(H, H)) (hfix : ∀ x ∈ B, f x = x) :
    Nonempty ((ContinuousMap.id H).HomotopyRel f B) := by
  let A : Set D := {x : D | ‖(x : V2)‖ = 1}
  let b : D := ⟨fun _ => 1, by simp⟩
  have hb : b ∈ A := by
    change ‖fun _ : Fin 2 => (1 : ℝ)‖ = 1
    simp
  let P : H ≃ₜ (D × AddCircle p) :=
    (Homeomorph.refl D).prodCongr hamiltonSolidTorusCircleEquiv
  let f' : C(D × AddCircle p, D × AddCircle p) :=
    (⟨P, P.continuous⟩ : C(H, D × AddCircle p)).comp
      (f.comp (⟨P.symm, P.symm.continuous⟩ : C(D × AddCircle p, H)))
  have hf' (x : D) (hx : x ∈ A) (z : AddCircle p) : f' (x, z) = (x, z) := by
    have hxB : P.symm (x, z) ∈ B := ⟨hx, mem_univ _⟩
    change P (f (P.symm (x, z))) = (x, z)
    rw [hfix _ hxB, P.apply_symm_apply]
  obtain ⟨G⟩ := (convex_closedBall (0 : V2) 1).exists_homotopyRel_circle_product
    isPreconnected_hamiltonDiskRim b hb p f' hf'
  refine ⟨{
    toFun := fun z => P.symm (G (z.1, P z.2))
    continuous_toFun := P.symm.continuous.comp
      (G.continuous.comp (continuous_fst.prodMk (P.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    rw [G.apply_zero]
    exact P.symm_apply_apply x
  · intro x
    rw [G.apply_one]
    change P.symm (P (f (P.symm (P x)))) = f x
    rw [P.symm_apply_apply, P.symm_apply_apply]
  · intro t x hx
    have hxA : P x ∈ A ×ˢ univ := ⟨hx.1, mem_univ _⟩
    change P.symm (G (t, P x)) = x
    rw [G.eq_fst t hxA]
    exact P.symm_apply_apply x

theorem exists_hamiltonSolidTorus_two_relative_homotopies
    (phi g : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (hg : ∀ x ∈ B, g x = x) :
    Nonempty (phi.HomotopyRel g B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel g B) := by
  obtain ⟨G⟩ := exists_hamiltonSolidTorus_identity_homotopy g hg
  exact ⟨⟨F.symm.trans G⟩, ⟨G⟩⟩

end PoincareConjecture.M76
