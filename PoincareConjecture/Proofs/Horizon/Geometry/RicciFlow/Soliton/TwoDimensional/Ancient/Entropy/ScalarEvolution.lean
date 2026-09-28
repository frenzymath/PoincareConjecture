import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

theorem ricciNormSq_eq_half_scalarCurvature_sq (D : LeviCivitaData g)
    (x : M) :
    D.ricciNormSq x = (1 / 2 : ℝ) * (D.scalarCurvature x) ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b := g.orthonormalBasis x
  have hinner (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hric (i j) :
      D.ricci x (b i) (b j) = D.scalarCurvature x / 2 * g.inner x (b i) (b j) :=
    D.ricci_eq_half_scalarCurvature_mul_inner x (b i) (b j)
  unfold ricciNormSq
  change (∑ i, ∑ j, (D.ricci x (b i) (b j)) ^ 2) = _
  simp only [hric, hinner, mul_ite, mul_one, mul_zero, ite_pow, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, hd, nsmul_eq_mul]
  ring

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}

theorem contMDiffAt_scalarCurvature_surface (F : RicciFlow 2 M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (t, x) := by
  have h := F.contMDiffAt_tensorTrace_fields
    (T := fun s => (F.connection s).ricciEvaluation) (k := 0) (x := x) ht
    (fun s => (F.connection s).ricciEvaluation_isSmooth_manifold)
    (fun X hX => F.contMDiffAt_ricci_fields ht (hX 0) (hX 1))
    (X := Fin.elim0) (fun i => Fin.elim0 i)
  exact h

theorem hasDerivAt_scalarCurvature_surface (F : RicciFlow 2 M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) :
    HasDerivAt (fun s => (F.connection s).scalarCurvature x)
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        ((F.connection t).scalarCurvature x) ^ 2) t := by
  convert F.hasDerivAt_scalarCurvature ht x using 1
  rw [(F.connection t).ricciNormSq_eq_half_scalarCurvature_sq]
  ring

end PoincareConjecture.RicciFlow
