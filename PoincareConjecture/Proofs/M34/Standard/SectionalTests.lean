import PoincareConjecture.Proofs.M34.Mathlib.AlternatingSectional
import PoincareConjecture.Proofs.M04.SectionalRayleigh
import PoincareConjecture.Proofs.M04.CurvatureSymmetries

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

open M04

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem sectional_lower_of_surjective_linearMap
    (D : LeviCivitaData g) (x : M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E →ₗ[ℝ] TangentSpace (𝓡 n) x) (hf : Function.Surjective f) (m : ℝ)
    (hmin : ∀ p q : E, ‖p‖ = 1 → ‖q‖ = 1 → inner ℝ p q = 0 →
      m * metricGram g x (f p) (f q) ≤
        D.curvatureTensor x (f p) (f q) (f p) (f q))
    (u v : TangentSpace (𝓡 n) x) :
    m * metricGram g x u v ≤ D.curvatureTensor x u v u v := by
  obtain ⟨R, hR⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  obtain ⟨G, hG⟩ := (isSmoothCovariantTensor_metricGramEvaluation g).1 x
  let A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
    (R - m • G).compLinearMap (fun _ => f)
  have hA (a b c d : E) : A ![a, b, c, d] =
      D.curvatureTensor x (f a) (f b) (f c) (f d) -
        m * (g.inner x (f a) (f c) * g.inner x (f b) (f d) -
          g.inner x (f a) (f d) * g.inner x (f b) (f c)) := by
    simp only [A, MultilinearMap.compLinearMap_apply, sub_apply, smul_apply,
      smul_eq_mul, ← hR, ← hG, LeviCivitaData.riemannEvaluation, metricGramEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hfirst (a b c d : E) : A ![a, b, c, d] = -A ![b, a, c, d] := by
    rw [hA, hA, curvatureTensor_swap_first D]
    ring
  have hlast (a b c d : E) : A ![a, b, c, d] = -A ![a, b, d, c] := by
    rw [hA, hA, curvatureTensor_swap_last D]
    ring
  have hdiag (a b : E) : A ![a, b, a, b] =
      D.curvatureTensor x (f a) (f b) (f a) (f b) - m * metricGram g x (f a) (f b) := by
    rw [hA, g.symm x (f b) (f a)]
    simp only [metricGram, pow_two]
  obtain ⟨a, rfl⟩ := hf u
  obtain ⟨b, rfl⟩ := hf v
  have h := A.sectional_nonneg_of_orthonormal hfirst hlast
    (fun p q hp hq hpq => by rw [hdiag]; exact sub_nonneg.mpr (hmin p q hp hq hpq)) a b
  rw [hdiag] at h
  exact sub_nonneg.mp h

theorem modelOrthonormalPairs_linearIndependent
    {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ modelOrthonormalPairs n) : LinearIndependent ℝ ![p.1, p.2] := by
  have horth : Orthonormal ℝ (![p.1, p.2] : Fin 2 → EuclideanSpace ℝ (Fin n)) := by
    constructor
    · intro i
      fin_cases i
      · exact hp.1
      · exact hp.2.1
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact hp.2.2
      · change inner ℝ p.2 p.1 = 0
        rw [real_inner_comm]
        exact hp.2.2
      · exact (hij rfl).elim
  exact horth.linearIndependent

end PoincareConjecture.M34
