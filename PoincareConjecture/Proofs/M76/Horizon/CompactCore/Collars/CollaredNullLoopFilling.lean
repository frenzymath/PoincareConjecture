import PoincareConjecture.Proofs.M76.Wall.ProtectedFrontierBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Metric unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

private theorem exists_nonzero_depth_extension
    (r : C(Q, Ioo (-1 : ℝ) 1)) (hr : ∀ u, (r u : ℝ) ≠ 0) :
    ∃ R : C(D, Ioo (-1 : ℝ) 1),
      (∀ u : Q, R ⟨u, sphere_subset_closedBall u.property⟩ = r u) ∧
      (∀ x, (R x : ℝ) ≠ 0) := by
  let : ConnectedSpace Q :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) 0 zero_le_one)
  have hc : Continuous (fun u => (r u : ℝ)) := continuous_subtype_val.comp r.continuous
  have hsign : (∀ u, 0 < (r u : ℝ)) ∨ (∀ u, (r u : ℝ) < 0) := by
    by_cases hp : ∀ u, 0 < (r u : ℝ)
    · exact Or.inl hp
    · push Not at hp
      obtain ⟨a, ha⟩ := hp
      right
      intro b
      by_contra hb
      have hb' : 0 ≤ (r b : ℝ) := le_of_not_gt hb
      obtain ⟨u, hu⟩ := intermediate_value_univ a b hc ⟨ha, hb'⟩
      exact hr u hu
  rcases hsign with hp | hn
  · let p : C(Q, Ioo (0 : ℝ) 1) :=
      ⟨fun u => ⟨r u, hp u, (r u).property.2⟩, hc.subtype_mk _⟩
    let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
      (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by constructor <;> norm_num⟩
    obtain ⟨R, hR⟩ := ContinuousMap.exists_closedBall_extension_of_contractible p
    let j : C(Ioo (0 : ℝ) 1, Ioo (-1 : ℝ) 1) :=
      ⟨fun t => ⟨t, by constructor <;> linarith [t.property.1, t.property.2]⟩, by fun_prop⟩
    refine ⟨j.comp R, ?_, fun x => ne_of_gt (R x).property.1⟩
    intro u
    change j (R _) = r u
    rw [hR]
    rfl
  · let p : C(Q, Ioo (-1 : ℝ) 0) :=
      ⟨fun u => ⟨r u, (r u).property.1, hn u⟩, hc.subtype_mk _⟩
    let : ContractibleSpace (Ioo (-1 : ℝ) 0) :=
      (convex_Ioo (-1 : ℝ) 0).contractibleSpace ⟨-1 / 2, by constructor <;> norm_num⟩
    obtain ⟨R, hR⟩ := ContinuousMap.exists_closedBall_extension_of_contractible p
    let j : C(Ioo (-1 : ℝ) 0, Ioo (-1 : ℝ) 1) :=
      ⟨fun t => ⟨t, by constructor <;> linarith [t.property.1, t.property.2]⟩, by fun_prop⟩
    refine ⟨j.comp R, ?_, fun x => ne_of_lt (R x).property.2⟩
    intro u
    change j (R _) = r u
    rw [hR]
    rfl

theorem PLDomain.exists_collared_null_loop_filling
    {X : Type*} [TopologicalSpace X] {F U : Set X}
    (G : (F × Ioo (-1 : ℝ) 1) ≃ₜ U)
    (hzero : ∀ z, (G z : X) ∈ F ↔ (z.2 : ℝ) = 0)
    (gamma : C(Q, F)) (A : C(I × Q, U))
    (hbase : ∀ u, A (0, u) = G (gamma u, ⟨0, by norm_num⟩))
    (houter : ∀ u, (A (1, u) : X) ∉ F)
    (hnull : gamma.Nullhomotopic) :
    ∃ fill : C(D, U),
      (∀ u : Q, fill ⟨u, sphere_subset_closedBall u.property⟩ = A (1, u)) ∧
      ∀ x : D, (fill x : X) ∉ F := by
  let B : C(I × Q, F × Ioo (-1 : ℝ) 1) :=
    ⟨fun z => G.symm (A z), G.symm.continuous.comp A.continuous⟩
  let beta : C(Q, F) := ⟨fun u => (B (1, u)).1, by fun_prop⟩
  let H : ContinuousMap.Homotopy gamma beta :=
    { toContinuousMap := ⟨fun z => (B z).1, continuous_fst.comp B.continuous⟩
      map_zero_left := by
        intro u
        change (G.symm (A (0, u))).1 = gamma u
        rw [hbase, G.symm_apply_apply]
      map_one_left := fun _ => rfl }
  have hbeta : beta.Nullhomotopic := by
    obtain ⟨y, hy⟩ := hnull
    exact ⟨y, (ContinuousMap.Homotopic.symm ⟨H⟩).trans hy⟩
  obtain ⟨baseFill, hbaseFill⟩ := hbeta.exists_closedBall_extension beta
  let r : C(Q, Ioo (-1 : ℝ) 1) := ⟨fun u => (B (1, u)).2, by fun_prop⟩
  have hr (u : Q) : (r u : ℝ) ≠ 0 := by
    intro hu
    apply houter u
    have hh := (hzero (B (1, u))).mpr hu
    change (G (G.symm (A (1, u))) : X) ∈ F at hh
    simpa only [G.apply_symm_apply] using hh
  obtain ⟨depthFill, hdepthFill, hdepth⟩ := exists_nonzero_depth_extension r hr
  let fill : C(D, U) :=
    ⟨fun x => G (baseFill x, depthFill x),
      G.continuous.comp (baseFill.continuous.prodMk depthFill.continuous)⟩
  refine ⟨fill, ?_, ?_⟩
  · intro u
    change G (baseFill _, depthFill _) = A (1, u)
    rw [hbaseFill, hdepthFill]
    exact G.apply_symm_apply (A (1, u))
  · intro x hx
    exact hdepth x ((hzero (baseFill x, depthFill x)).mp hx)

end PoincareConjecture.M76
