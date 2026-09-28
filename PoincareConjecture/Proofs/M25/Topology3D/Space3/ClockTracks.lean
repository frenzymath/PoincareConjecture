import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockFlow











set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (V : ℝ × E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)

include hK

omit [NormedSpace ℝ E] [CompleteSpace E] in


theorem clockField_slice_lipschitz (t : ℝ) : LipschitzWith K (fun x => V (t, x)) := by
  simpa only [one_mul, mul_one, Function.comp_def, clockField] using
    LipschitzWith.prod_snd.comp (hK.comp (LipschitzWith.prodMk_left t))



theorem clockEvolution_tracks (γ : ℝ → E) {a b s : ℝ} (hs : s ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (V (t, γ t)) t) :
    EqOn (fun t => clockEvolution V hK hL s t (γ s)) γ (Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun t x => V (t, x)) (s := fun _ => univ)
    (fun t _ => (clockField_slice_lipschitz V hK t).lipschitzOnWith) hs
  · exact fun t _ => ⟨clockEvolution_hasDerivAt V hK hL s t (γ s), mem_univ _⟩
  · exact fun t ht => ⟨hγ t ht, mem_univ _⟩
  · exact clockEvolution_self V hK hL s (γ s)



theorem clockEvolution_eq_self (x : E) (hx : ∀ u, V (u, x) = 0) (s t : ℝ) :
    clockEvolution V hK hL s t x = x := by
  have hs : s ∈ Ioo (min s t - 1) (max s t + 1) :=
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
  have ht : t ∈ Ioo (min s t - 1) (max s t + 1) :=
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩
  exact clockEvolution_tracks V hK hL (fun _ => x) hs
    (fun u _ => by rw [hx]; exact hasDerivAt_const u x) ht



theorem clockEvolution_support_subset (s t : ℝ) :
    Function.support (fun x => clockEvolution V hK hL s t x - x) ⊆
      Prod.snd '' tsupport V := by
  intro x hx
  by_contra hxS
  have hz (u : ℝ) : V (u, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hxS ⟨(u, x), hp, rfl⟩
  exact hx (sub_eq_zero.mpr (clockEvolution_eq_self V hK hL x hz s t))



theorem clockEvolution_hasCompactSupport (hV : HasCompactSupport V) (s t : ℝ) :
    HasCompactSupport (fun x => clockEvolution V hK hL s t x - x) := by
  have hcompact : IsCompact (Prod.snd '' tsupport V) := hV.isCompact.image continuous_snd
  exact hcompact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (clockEvolution_support_subset V hK hL s t) hcompact.isClosed)

end PoincareConjecture.M25.Topology3D
