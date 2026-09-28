import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (ℝ × V2)
local notation "Q" => sphere (0 : V2) 1
local notation "E" => Set.prod (Icc (-1 : ℝ) 1)
  (Set.preimage (norm : V2 → ℝ) (Icc (1 : ℝ) 2))

private theorem exists_disk_filling_of_real_angular_lift
    (A : V ≃ₜ V) (gamma : C(Q, A '' E))
    (zeta : C(ℝ, Q)) (ell : C(Q, ℝ))
    (hangle : ∀ u : Q,
      (A.symm (gamma u)).2 = ‖(A.symm (gamma u)).2‖ • (zeta (ell u) : V2)) :
    ∃ F : C(closedBall (0 : V2) 1, A '' E),
      ∀ u : Q, F ⟨u, sphere_subset_closedBall u.property⟩ = gamma u := by
  let J := Icc (-1 : ℝ) 1
  let R := Icc (1 : ℝ) 2
  let Y := J × (R × ℝ)
  let : ContractibleSpace J :=
    (convex_Icc (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  let : ContractibleSpace R :=
    (convex_Icc (1 : ℝ) 2).contractibleSpace ⟨1, by norm_num⟩
  let h : C(Q, V) :=
    ⟨fun u => A.symm (gamma u),
      A.symm.continuous.comp (continuous_subtype_val.comp gamma.continuous)⟩
  have hh (u : Q) : h u ∈ E := by
    obtain ⟨x, hx, hxe⟩ := (gamma u).property
    change A.symm (gamma u) ∈ E
    rw [← hxe, A.symm_apply_apply]
    exact hx
  let s : C(Q, J) :=
    ⟨fun u => ⟨(h u).1, (hh u).1⟩, h.continuous.fst.subtype_mk _⟩
  let rad : C(Q, R) :=
    ⟨fun u => ⟨‖(h u).2‖, (hh u).2⟩, h.continuous.snd.norm.subtype_mk _⟩
  let lifted : C(Q, Y) := s.prodMk (rad.prodMk ell)
  obtain ⟨G, hG⟩ := lifted.exists_closedBall_extension_of_contractible
  have hnorm (u : Q) : ‖(u : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  let polar : C(Y, A '' E) :=
    ⟨fun y => ⟨A ((y.1 : ℝ), (y.2.1 : ℝ) • (zeta y.2.2 : V2)),
      ⟨((y.1 : ℝ), (y.2.1 : ℝ) • (zeta y.2.2 : V2)),
        ⟨y.1.property, by
          change ‖(y.2.1 : ℝ) • (zeta y.2.2 : V2)‖ ∈ Icc (1 : ℝ) 2
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (le_trans (by norm_num) y.2.1.property.1), hnorm, mul_one]
          exact y.2.1.property⟩, rfl⟩⟩,
      (A.continuous.comp (continuous_fst.subtype_val.prodMk
        (continuous_snd.fst.subtype_val.smul
          (continuous_subtype_val.comp (zeta.continuous.comp continuous_snd.snd))))).subtype_mk _⟩
  refine ⟨polar.comp G, ?_⟩
  intro u
  change polar (G ⟨u, sphere_subset_closedBall u.property⟩) = gamma u
  rw [hG]
  apply Subtype.ext
  change A ((A.symm (gamma u)).1,
    ‖(A.symm (gamma u)).2‖ • (zeta (ell u) : V2)) = gamma u
  rw [← hangle]
  exact A.apply_symm_apply _






theorem exists_retracted_disk_filling_of_real_angular_lift
    (A : V ≃ₜ V) (E1 : Set V) (hE1 : E1 ⊆ A '' E)
    (r : C(A '' E, E1))
    (hfix : ∀ x : A '' E, (x : V) ∈ E1 → (r x : V) = x)
    (gamma : C(Q, E1)) (zeta : C(ℝ, Q)) (ell : C(Q, ℝ))
    (hangle : ∀ u : Q,
      (A.symm (gamma u)).2 = ‖(A.symm (gamma u)).2‖ • (zeta (ell u) : V2)) :
    ∃ F : C(closedBall (0 : V2) 1, E1),
      ∀ u : Q, F ⟨u, sphere_subset_closedBall u.property⟩ = gamma u := by
  let inc : C(E1, A '' E) :=
    ⟨fun x => ⟨x, hE1 x.property⟩, continuous_subtype_val.subtype_mk _⟩
  obtain ⟨F0, hF0⟩ := exists_disk_filling_of_real_angular_lift A (inc.comp gamma)
    zeta ell hangle
  refine ⟨r.comp F0, ?_⟩
  intro u
  change r (F0 ⟨u, sphere_subset_closedBall u.property⟩) = gamma u
  rw [hF0]
  apply Subtype.ext
  exact hfix (inc (gamma u)) (gamma u).property

end PoincareConjecture.M76.HamiltonIndexOne
