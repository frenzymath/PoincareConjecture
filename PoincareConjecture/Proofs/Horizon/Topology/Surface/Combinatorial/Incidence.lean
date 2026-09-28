


import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Relation

















set_option autoImplicit false

namespace PoincareConjecture.Surface.Combinatorial.Incidence

open Matrix




def EndpointConnected {V E : Type*} (ends : E → V × V) : Prop :=
  ∀ v w, Relation.EqvGen (fun a b => ∃ e, ends e = (a, b)) v w


noncomputable def incidenceMatrix {V E : Type*}
    (ends : E → V × V) : Matrix E V (ZMod 2) := by
  classical
  exact fun e v =>
    (if (ends e).1 = v then 1 else 0) + (if (ends e).2 = v then 1 else 0)

@[simp]
theorem incidenceMatrix_mulVec_apply {V E : Type*} [Fintype V]
    (ends : E → V × V) (x : V → ZMod 2) (e : E) :
    (incidenceMatrix ends).mulVec x e = x (ends e).1 + x (ends e).2 := by
  classical
  simp only [incidenceMatrix, Matrix.mulVec, dotProduct]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp




theorem mem_ker_incidenceMatrix_iff {V E : Type*} [Fintype V] [Nonempty V]
    (ends : E → V × V) (hc : EndpointConnected ends) (x : V → ZMod 2) :
    x ∈ LinearMap.ker (incidenceMatrix ends).mulVecLin ↔
      ∃ c : ZMod 2, x = fun _ => c := by
  classical
  constructor
  · intro hx
    let v₀ : V := Classical.choice (inferInstance : Nonempty V)
    have hstep : ∀ {a b : V}, (∃ e, ends e = (a, b)) → x a = x b := by
      rintro a b ⟨e, he⟩
      have heq : (incidenceMatrix ends).mulVec x e = 0 := by
        have hx' := LinearMap.mem_ker.mp hx
        simpa [Matrix.mulVecLin_apply] using congrFun hx' e
      have heq' : x a + x b = 0 := by
        simpa [he, incidenceMatrix_mulVec_apply] using heq
      simpa [ZMod.neg_eq_self_mod_two] using eq_neg_of_add_eq_zero_left heq'
    have hconst : ∀ {a b : V},
        Relation.EqvGen (fun a b => ∃ e, ends e = (a, b)) a b → x a = x b := by
      intro a b hab
      induction hab with
      | rel a b hab => exact hstep hab
      | refl a => rfl
      | symm a b hab ih => exact ih.symm
      | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂
    refine ⟨x v₀, funext (fun v => ?_)⟩
    exact (hconst (hc v₀ v)).symm
  · rintro ⟨c, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext e
    simp only [Matrix.mulVecLin_apply, incidenceMatrix_mulVec_apply]
    exact CharTwo.add_self_eq_zero c



private lemma rank_add_ker_eq_card {V E : Type*} [Fintype V] [Fintype E]
    (A : Matrix E V (ZMod 2)) :
    A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = Fintype.card V := by
  classical
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

private lemma rank_ge_card_sub_one {V E : Type*} [Fintype V] [Fintype E]
    [Nonempty V] (ends : E → V × V) (hc : EndpointConnected ends) :
    Fintype.card V - 1 ≤ (incidenceMatrix ends).rank := by
  classical
  let oneV : V → ZMod 2 := fun _ => 1
  have hker_le : LinearMap.ker (incidenceMatrix ends).mulVecLin ≤
      (ZMod 2) ∙ oneV := by
    intro x hx
    obtain ⟨c, hxc⟩ := (mem_ker_incidenceMatrix_iff ends hc x).mp hx
    rw [hxc]
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c, by ext; simp [oneV]⟩
  have hker_dim : Module.finrank (ZMod 2)
      (LinearMap.ker (incidenceMatrix ends).mulVecLin) ≤ 1 := by
    have hone : oneV ≠ 0 := by
      intro h
      have hh := congrFun h (Classical.choice (inferInstance : Nonempty V))
      simpa [oneV] using hh
    calc
      _ ≤ Module.finrank (ZMod 2) ((ZMod 2) ∙ oneV) :=
        Submodule.finrank_mono hker_le
      _ = 1 := finrank_span_singleton hone
  have hrank := rank_add_ker_eq_card (incidenceMatrix ends)
  omega





theorem eulerCount_le_two {V E F : Type*}
    [Fintype V] [Fintype E] [Fintype F] [Nonempty V] [Nonempty F]
    (ends : E → V × V) (adjacentFaces : E → F × F)
    (hV : EndpointConnected ends)
    (hF : EndpointConnected adjacentFaces)
    (hboundary : (incidenceMatrix ends).transpose *
      incidenceMatrix adjacentFaces = 0) :
    (Fintype.card V : ℤ) - Fintype.card E + Fintype.card F ≤ 2 := by
  classical
  let A := incidenceMatrix ends
  let B := incidenceMatrix adjacentFaces
  have hrankA : Fintype.card V - 1 ≤ A.rank := by
    simpa [A] using rank_ge_card_sub_one ends hV
  have hrankB : Fintype.card F - 1 ≤ B.rank := by
    simpa [B] using rank_ge_card_sub_one adjacentFaces hF
  have hcomp : LinearMap.range B.mulVecLin ≤ LinearMap.ker A.transpose.mulVecLin := by
    rw [LinearMap.range_le_ker_iff]
    rw [← Matrix.mulVecLin_mul]
    simpa [A, B] using congrArg Matrix.mulVecLin hboundary
  have hdimB : Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) = B.rank := by
    have h := Matrix.rank_eq_finrank_range_toLin B (Pi.basisFun (ZMod 2) E)
      (Pi.basisFun (ZMod 2) F)
    rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] at h
    exact h.symm
  have hdimKer : Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin) =
      Fintype.card E - A.rank := by
    have hrankT := rank_add_ker_eq_card A.transpose
    have hrankT' : A.rank + Module.finrank (ZMod 2)
        (LinearMap.ker A.transpose.mulVecLin) = Fintype.card E := by
      calc
        A.rank + Module.finrank (ZMod 2)
            (LinearMap.ker A.transpose.mulVecLin) = A.transpose.rank +
              Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin) := by
                simpa using congrArg (fun r : ℕ => r +
                  Module.finrank (ZMod 2) (LinearMap.ker A.transpose.mulVecLin))
                  (Matrix.rank_transpose A).symm
        _ = Fintype.card E := hrankT
    omega
  have hdim_le : B.rank ≤ Fintype.card E - A.rank := by
    rw [← hdimB, ← hdimKer]
    exact Submodule.finrank_mono hcomp
  have hArank_le : A.rank ≤ Fintype.card E := by
    exact A.rank_le_card_height
  have hcardE : A.rank + B.rank ≤ Fintype.card E := by
    omega
  have hA_int : (Fintype.card V : ℤ) - 1 ≤ (A.rank : ℤ) := by
    have hcast : ((Fintype.card V - 1 : ℕ) : ℤ) =
        (Fintype.card V : ℤ) - 1 := by
      rw [Nat.cast_sub (m := 1) (n := Fintype.card V)
        (Nat.succ_le_of_lt (Fintype.card_pos (α := V)))]
      norm_num
    rw [← hcast]
    exact_mod_cast hrankA
  have hB_int : (Fintype.card F : ℤ) - 1 ≤ (B.rank : ℤ) := by
    have hcast : ((Fintype.card F - 1 : ℕ) : ℤ) =
        (Fintype.card F : ℤ) - 1 := by
      rw [Nat.cast_sub (m := 1) (n := Fintype.card F)
        (Nat.succ_le_of_lt (Fintype.card_pos (α := F)))]
      norm_num
    rw [← hcast]
    exact_mod_cast hrankB
  have hE_int : (A.rank : ℤ) + (B.rank : ℤ) ≤ Fintype.card E := by
    exact_mod_cast hcardE
  omega

end PoincareConjecture.Surface.Combinatorial.Incidence
