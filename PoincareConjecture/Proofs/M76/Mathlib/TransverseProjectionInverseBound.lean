import PoincareConjecture.Proofs.M76.Mathlib.SecantTransversality









set_option autoImplicit false

open Set
open scoped NNReal

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_inverse_secant_bound_of_ker_transverse (Q : E →L[ℝ] F)
    (J : F →L[ℝ] E) (hJ : Function.RightInverse J Q) {S : Set E}
    (htrans : Q.ker.IsSecantTransverse S) :
    ∃ K : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ K * ‖Q x - Q y‖ := by
  obtain ⟨c, hc, hb⟩ := htrans
  let K : ℝ≥0 := ⟨‖J‖ / c, div_nonneg (norm_nonneg J) hc.le⟩
  refine ⟨K, fun x hx y hy => ?_⟩
  let v := x - y
  have hv : v - J (Q v) ∈ Q.ker := by
    change Q (v - J (Q v)) = 0
    rw [map_sub, hJ, sub_self]
  have hzero : Q.kerᗮ.starProjection (v - J (Q v)) = 0 :=
    Q.kerᗮ.starProjection_apply_eq_zero_iff.mpr (by simpa using hv)
  have hproj : Q.kerᗮ.starProjection v = Q.kerᗮ.starProjection (J (Q v)) :=
    sub_eq_zero.mp (by simpa only [map_sub] using hzero)
  have hbound : c * ‖v‖ ≤ ‖J‖ * ‖Q v‖ := by
    calc
      c * ‖v‖ ≤ ‖v - Q.ker.starProjection v‖ := hb x hx y hy
      _ = ‖Q.kerᗮ.starProjection v‖ := by rw [Q.ker.starProjection_orthogonal_val]
      _ = ‖Q.kerᗮ.starProjection (J (Q v))‖ := congrArg norm hproj
      _ ≤ ‖J (Q v)‖ := Q.kerᗮ.norm_starProjection_apply_le _
      _ ≤ ‖J‖ * ‖Q v‖ := J.le_opNorm _
  change ‖v‖ ≤ (‖J‖ / c) * ‖Q x - Q y‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  simpa only [v, map_sub, mul_comm c ‖x - y‖] using hbound

end ContinuousLinearMap
