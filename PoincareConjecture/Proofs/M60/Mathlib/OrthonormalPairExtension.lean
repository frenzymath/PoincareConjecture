import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic









set_option autoImplicit false

namespace PoincareConjecture.M60

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem exists_orthonormalBasis_pair (hdim : Module.finrank ℝ E = 3)
    (u v : E) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E, b 0 = u ∧ b 1 = v := by
  let w : Fin 3 → E := ![u, v, 0]
  let s : Set (Fin 3) := {i | i < 2}
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have horth : Orthonormal ℝ (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    change i < 2 at hi
    change j < 2 at hj
    have hi' : i = 0 ∨ i = 1 := by omega
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · change inner ℝ u u = 1
      exact hu
    · change inner ℝ u v = 0
      exact huv
    · change inner ℝ v u = 0
      exact hvu
    · change inner ℝ v v = 1
      exact hv
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using hdim)
  exact ⟨b, hb 0 (by decide), hb 1 (by decide)⟩

end PoincareConjecture.M60
