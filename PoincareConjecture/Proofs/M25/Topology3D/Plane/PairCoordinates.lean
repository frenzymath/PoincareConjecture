import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

set_option autoImplicit false

namespace PoincareConjecture.M25.Topology3D

open Module

theorem exists_linearEquiv_map_pair {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (hdim : Module.finrank K E = 2)
    {u v : E} (hli : LinearIndependent K ![u, v]) :
    ∃ e : E ≃ₗ[K] (K × K), e u = (1, 0) ∧ e v = (0, 1) := by
  let b : Basis (Fin 2) K E :=
    basisOfLinearIndependentOfCardEqFinrank' ![u, v] hli (by simp [hdim])
  have hb0 : b 0 = u := by simp [b]
  have hb1 : b 1 = v := by simp [b]
  refine ⟨b.equiv (Basis.finTwoProd K) (Equiv.refl (Fin 2)), ?_, ?_⟩
  · rw [← hb0]
    simp
  · rw [← hb1]
    simp

theorem exists_continuousAffineEquiv_map_triangle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {q a b : E}
    (hli : LinearIndependent ℝ ![a - q, b - q]) :
    ∃ f : E ≃ᴬ[ℝ] (ℝ × ℝ), f q = (0, 0) ∧ f a = (1, 0) ∧ f b = (0, 1) := by
  obtain ⟨e, hea, heb⟩ := exists_linearEquiv_map_pair hdim hli
  let f := (ContinuousAffineEquiv.vaddConst ℝ q).symm.trans
    e.toContinuousLinearEquiv.toContinuousAffineEquiv
  refine ⟨f, ?_, ?_, ?_⟩
  · change e (q - q) = (0, 0)
    rw [sub_self, map_zero]
    rfl
  · change e (a - q) = (1, 0)
    exact hea
  · change e (b - q) = (0, 1)
    exact heb

end PoincareConjecture.M25.Topology3D
