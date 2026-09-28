import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence
import PoincareConjecture.Proofs.M64.Mathlib.SupportMinimal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace PoincareConjecture

open PoincareConjecture.Surface.Combinatorial.Incidence

theorem m64Intrinsic_region_euler_upper_bound_of_external_face
    {V E F : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    [Nonempty V] [Nonempty F]
    (ends : E → V × V)
    (adjacentFaces : E → (Sum F Unit) × (Sum F Unit))
    (hV : EndpointConnected ends)
    (hF : EndpointConnected adjacentFaces)
    (hboundary : (incidenceMatrix ends).transpose *
      incidenceMatrix adjacentFaces = 0) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F ≤ 1 := by
  have hclosed := eulerCount_le_two ends adjacentFaces hV hF hboundary
  have hsum : Fintype.card (Sum F Unit) = Fintype.card F + 1 := by
    simp
  rw [hsum] at hclosed
  omega

private lemma m64_rank_add_ker_eq_card {V E : Type*} [Fintype V] [Finite E]
    (A : Matrix E V (ZMod 2)) :
    A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = Fintype.card V := by
  classical
  let _ := Fintype.ofFinite E
  have hrank : A.rank = Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) := by
    have h := Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun (ZMod 2) E)
      (Pi.basisFun (ZMod 2) V)
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] at h
    exact h
  calc
    A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
        Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
          Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) := by rw [hrank]
    _ = Module.finrank (ZMod 2) (V → ZMod 2) := by
      exact LinearMap.finrank_range_add_finrank_ker
        (K := ZMod 2) (V := V → ZMod 2) (V₂ := E → ZMod 2) A.mulVecLin
    _ = Fintype.card V := by simp

private lemma m64_rank_eq_card_sub_one_of_connected
    {V E : Type*} [Fintype V] [Finite E] [Nonempty V]
    (ends : E → V × V) (hconnected : EndpointConnected ends) :
    (incidenceMatrix ends).rank + 1 = Fintype.card V := by
  classical
  let _ := Fintype.ofFinite E
  let A := incidenceMatrix ends
  let oneV : V → ZMod 2 := fun _ => 1
  have hone : oneV ≠ 0 := by
    intro h
    have hh := congrFun h (Classical.choice (inferInstance : Nonempty V))
    simp [oneV] at hh
  have hker_eq : LinearMap.ker A.mulVecLin = (ZMod 2) ∙ oneV := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hxc⟩ := (mem_ker_incidenceMatrix_iff ends hconnected x).mp hx
      rw [hxc]
      exact Submodule.mem_span_singleton.mpr ⟨c, by ext; simp [oneV]⟩
    · intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      rw [← hc]
      apply LinearMap.mem_ker.mpr
      funext e
      change (incidenceMatrix ends).mulVec (c • oneV) e = 0
      simpa [incidenceMatrix_mulVec_apply, oneV] using CharTwo.add_self_eq_zero c
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = 1 := by
    rw [hker_eq]
    exact finrank_span_singleton hone
  have hrank := m64_rank_add_ker_eq_card A
  rw [hdim] at hrank
  simpa [A] using hrank

private lemma m64_rank_add_one_le_card
    {V E : Type*} [Fintype V] [Finite E] [Nonempty V]
    (ends : E → V × V) :
    (incidenceMatrix ends).rank + 1 ≤ Fintype.card V := by
  classical
  let _ := Fintype.ofFinite E
  let oneV : V → ZMod 2 := fun _ => 1
  have hone : oneV ≠ 0 := by
    intro h
    have hh := congrFun h (Classical.choice (inferInstance : Nonempty V))
    simp [oneV] at hh
  have hspan : (ZMod 2) ∙ oneV ≤ LinearMap.ker (incidenceMatrix ends).mulVecLin := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply LinearMap.mem_ker.mpr
    funext e
    change (incidenceMatrix ends).mulVec oneV e = 0
    simpa only [incidenceMatrix_mulVec_apply, oneV] using
      CharTwo.add_self_eq_zero (1 : ZMod 2)
  have hdim : 1 ≤ Module.finrank (ZMod 2)
      (LinearMap.ker (incidenceMatrix ends).mulVecLin) := by
    calc
      1 = Module.finrank (ZMod 2) ((ZMod 2) ∙ oneV) :=
        (finrank_span_singleton hone).symm
      _ ≤ _ := Submodule.finrank_mono hspan
  have hrank := m64_rank_add_ker_eq_card (incidenceMatrix ends)
  omega

theorem m64Intrinsic_region_euler_ge_one_of_capped_cycle_fill
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [Nonempty V]
    (ends : E → V × V)
    (adjacentFaces : E → (Sum F Unit) × (Sum F Unit))
    (hfill : LinearMap.ker (incidenceMatrix ends).transpose.mulVecLin ≤
      LinearMap.range (incidenceMatrix adjacentFaces).mulVecLin) :
    (1 : ℤ) ≤ (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F := by
  classical
  let A := incidenceMatrix ends
  let B := incidenceMatrix adjacentFaces
  have hA : A.rank + 1 ≤ Fintype.card V := m64_rank_add_one_le_card ends
  have hB : B.rank + 1 ≤ Fintype.card (Sum F Unit) :=
    m64_rank_add_one_le_card adjacentFaces
  have hdimB : Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) = B.rank := by
    have h := Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun (ZMod 2) E)
      (Pi.basisFun (ZMod 2) (Sum F Unit))
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] at h
    exact h.symm
  have hker : Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin) ≤ B.rank := by
    rw [← hdimB]
    exact Submodule.finrank_mono hfill
  have hrank := m64_rank_add_ker_eq_card A.transpose
  rw [Matrix.rank_transpose] at hrank
  have hsum : Fintype.card (Sum F Unit) = Fintype.card F + 1 := by simp
  have hcard : Fintype.card E + 1 ≤ Fintype.card V + Fintype.card F := by omega
  have hcard' : (Fintype.card E : ℤ) + 1 ≤ Fintype.card V + Fintype.card F := by
    exact_mod_cast hcard
  omega

theorem m64Intrinsic_region_euler_ge_one_of_minimal_cycle_fill
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [Nonempty V]
    (ends : E → V × V)
    (adjacentFaces : E → (Sum F Unit) × (Sum F Unit))
    (hfill : ∀ x ∈ LinearMap.ker (incidenceMatrix ends).transpose.mulVecLin, x ≠ 0 →
      (∀ y ∈ LinearMap.ker (incidenceMatrix ends).transpose.mulVecLin,
        y ≠ 0 → Function.support y ⊆ Function.support x →
          Function.support x ⊆ Function.support y) →
      x ∈ LinearMap.range (incidenceMatrix adjacentFaces).mulVecLin) :
    (1 : ℤ) ≤ (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F := by
  apply m64Intrinsic_region_euler_ge_one_of_capped_cycle_fill ends adjacentFaces
  exact Submodule.le_of_mem_of_support_minimal _ _ hfill

theorem m64Intrinsic_region_euler_eq_one_of_capped_exactness
    {V E F : Type*}
    [Fintype V] [Fintype E] [Fintype F]
    [Nonempty V] [Nonempty F]
    (ends : E → V × V)
    (adjacentFaces : E → (Sum F Unit) × (Sum F Unit))
    (hV : EndpointConnected ends)
    (hF : EndpointConnected adjacentFaces)
    (hExact : LinearMap.range (incidenceMatrix adjacentFaces).mulVecLin =
      LinearMap.ker (incidenceMatrix ends).transpose.mulVecLin) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F = 1 := by
  classical
  let A := incidenceMatrix ends
  let B := incidenceMatrix adjacentFaces
  have hA : A.rank + 1 = Fintype.card V :=
    m64_rank_eq_card_sub_one_of_connected ends hV
  have hB : B.rank + 1 = Fintype.card (Sum F Unit) :=
    m64_rank_eq_card_sub_one_of_connected adjacentFaces hF
  have hdimB : Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) = B.rank := by
    have h := Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun (ZMod 2) E)
      (Pi.basisFun (ZMod 2) (Sum F Unit))
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] at h
    exact h.symm
  have hdimKer : A.rank +
      Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin) = Fintype.card E := by
    have h := m64_rank_add_ker_eq_card A.transpose
    rw [Matrix.rank_transpose] at h
    exact h
  have hExactDim : Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin) :=
    congrArg (fun S : Submodule (ZMod 2) (E → ZMod 2) =>
      Module.finrank (ZMod 2) S) hExact
  rw [hdimB] at hExactDim
  have hrankSum : A.rank + B.rank = Fintype.card E := by
    omega
  have hsum : Fintype.card (Sum F Unit) = Fintype.card F + 1 := by simp
  have hA' : (A.rank : ℤ) + 1 = Fintype.card V := by exact_mod_cast hA
  have hB' : (B.rank : ℤ) + 1 = Fintype.card (Sum F Unit) := by exact_mod_cast hB
  have hsum' : (Fintype.card (Sum F Unit) : ℤ) = Fintype.card F + 1 := by
    exact_mod_cast hsum
  have hrankSum' : (A.rank : ℤ) + B.rank = Fintype.card E := by
    exact_mod_cast hrankSum
  omega

theorem m64Intrinsic_region_curvature_lower_bound_of_euler_ge_one
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    {R : ℝ}
    (hcurvature :
      2 * Real.pi *
          ((Fintype.card V : ℝ) - Fintype.card E + Fintype.card F) -
        Real.pi ≤ R)
    (heuler : (1 : ℤ) ≤
      (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F) :
    Real.pi ≤ R := by
  have heuler' : (1 : ℝ) ≤
      (Fintype.card V : ℝ) - Fintype.card E + Fintype.card F := by
    exact_mod_cast heuler
  nlinarith [Real.pi_pos]

end PoincareConjecture
