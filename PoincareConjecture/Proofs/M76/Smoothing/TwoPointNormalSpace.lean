import PoincareConjecture.Proofs.M76.Mathlib.TwoRayProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false

open Set Geometry ContinuousLinearMap

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem rightInverse_rayFrame_iff (u : E) (Q : E →L[ℝ] ℝ) :
    Function.RightInverse (toSpanSingleton ℝ u) Q ↔ Q u = 1 := by
  constructor
  · intro h
    simpa only [toSpanSingleton_apply_one] using h 1
  · intro h r
    change Q (r • u) = r
    rw [map_smul, h, smul_eq_mul, mul_one]

theorem convex_twoPointOperatorSet (u v : E) :
    Convex ℝ {Q : E →L[ℝ] ℝ | Q u = 1 ∧ Q v < 0} := by
  intro Q hQ R hR a b ha hb hab
  constructor
  · change a * Q u + b * R u = 1
    rw [hQ.1, hR.1, mul_one, mul_one, hab]
  · change a * Q v + b * R v < 0
    exact convex_Iio (0 : ℝ) hQ.2 hR.2 ha hb hab

noncomputable def twoPointFrameEmbeddingHomeomorph (u v : E)
    (hv : LinearIndependent ℝ ![u, v]) :
    FrameEmbeddingSpace (toSpanSingleton ℝ u) (twoRayStar u v) ≃ₜ
      {Q : E →L[ℝ] ℝ // Q u = 1 ∧ Q v < 0} :=
  Homeomorph.setCongr (by
    ext Q
    change (Function.RightInverse (toSpanSingleton ℝ u) Q ∧ InjOn Q (twoRayStar u v)) ↔ _
    rw [rightInverse_rayFrame_iff]
    exact and_congr_right (fun hu => injOn_twoRayStar_iff u v hv Q hu))

end PoincareConjecture.M76.Smoothing

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem nonempty_twoPointOperatorSet (u v : E) (hv : LinearIndependent ℝ ![u, v]) :
    ({Q : E →L[ℝ] ℝ | Q u = 1 ∧ Q v < 0} : Set (E →L[ℝ] ℝ)).Nonempty := by
  let V := Submodule.span ℝ (range ![u, v])
  let b : Module.Basis (Fin 2) ℝ V := Module.Basis.span hv
  let A : V →L[ℝ] ℝ := (b.coord 0 - b.coord 1).toContinuousLinearMap
  let Q : E →L[ℝ] ℝ := A.comp V.orthogonalProjectionOnto
  have hzero : (b 0 : E) = u := Module.Basis.coe_span_apply hv 0
  have hone : (b 1 : E) = v := Module.Basis.coe_span_apply hv 1
  refine ⟨Q, ?_, ?_⟩
  · rw [← hzero]
    simp [Q, A, Module.Basis.coord_apply]
  · rw [← hone]
    simp [Q, A, Module.Basis.coord_apply]

theorem contractible_twoPointFrameEmbeddingSpace (u v : E)
    (hv : LinearIndependent ℝ ![u, v]) :
    ContractibleSpace (FrameEmbeddingSpace (toSpanSingleton ℝ u) (twoRayStar u v)) := by
  let : ContractibleSpace {Q : E →L[ℝ] ℝ // Q u = 1 ∧ Q v < 0} :=
    (convex_twoPointOperatorSet u v).contractibleSpace (nonempty_twoPointOperatorSet u v hv)
  exact (twoPointFrameEmbeddingHomeomorph u v hv).contractibleSpace

end PoincareConjecture.M76.Smoothing
