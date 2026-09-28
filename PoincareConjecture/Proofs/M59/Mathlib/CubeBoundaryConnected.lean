import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open Set
open scoped unitInterval Topology

namespace Cube

variable {N : Type*}

private instance : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_le_one⟩

theorem contractibleSpace (N : Type*) : ContractibleSpace (I^N) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨fun _ => 0, ⟨{
    toFun := fun v i => unitInterval.symm v.1 * v.2 i
    continuous_toFun := by
      apply continuous_pi
      intro i
      apply Continuous.subtype_mk
      change Continuous (fun v : I × (I^N) => (1 - (v.1 : ℝ)) * (v.2 i : ℝ))
      fun_prop
    map_zero_left := by intro v; ext i; simp
    map_one_left := by intro v; ext i; simp }⟩⟩

theorem isPathConnected_face (i : N) (c : I) :
    IsPathConnected {v : I^N | v i = c} := by
  classical
  have h (j : N) : IsPathConnected (if j = i then ({c} : Set I) else univ) := by
    split_ifs
    · exact isPathConnected_singleton c
    · exact isPathConnected_univ
  convert IsPathConnected.pi h using 1
  ext v
  simp only [mem_ofPred_eq, mem_univ_pi]
  constructor
  · intro hv j
    by_cases hj : j = i
    · simpa [hj] using hv
    · simp [hj]
  · intro hv
    simpa using hv i

theorem isPathConnected_boundary [Nontrivial N] : IsPathConnected (boundary N) := by
  classical
  let z : I^N := fun _ => 0
  have hz : z ∈ boundary N := ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩
  refine ⟨z, hz, ?_⟩
  intro v hv
  obtain ⟨i, hi⟩ := hv
  obtain ⟨j, hji⟩ := exists_ne i
  let w : I^N := Function.update z i (v i)
  have hwi : w i = v i := by simp [w]
  have hwj : w j = 0 := by simp [w, z, hji]
  have hfirst : JoinedIn (boundary N) v w :=
    ((isPathConnected_face i (v i)).joinedIn v rfl w hwi).mono
      (fun u hu => ⟨i, hu ▸ hi⟩)
  have hsecond : JoinedIn (boundary N) w z :=
    ((isPathConnected_face j 0).joinedIn w hwj z rfl).mono
      (fun u hu => ⟨j, Or.inl hu⟩)
  exact (hfirst.trans hsecond).symm

end Cube
