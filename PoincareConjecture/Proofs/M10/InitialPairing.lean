import PoincareConjecture.Proofs.M10.InitialGram









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M10

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*}


theorem bilinear_apply_eq_basis_sum [Fintype ι] (b : Module.Basis ι ℝ E)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    B u v = ∑ i, ∑ j, (b.repr u i * b.repr v j) * B (b i) (b j) := by
  calc
    B u v = B (∑ i, b.repr u i • b i) (∑ j, b.repr v j • b j) := by
      rw [b.sum_repr, b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring


theorem tendsto_bilinear_apply_of_basis [Finite ι] {α : Type*} {l : Filter α}
    (b : Module.Basis ι ℝ E) {B : α → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ}
    (h : ∀ i j, Tendsto (fun a ↦ B a (b i) (b j)) l (𝓝 (B₀ (b i) (b j)))) (u v : E) :
    Tendsto (fun a ↦ B a u v) l (𝓝 (B₀ u v)) := by
  let := Fintype.ofFinite ι
  have hf : (fun a ↦ B a u v) =
      (fun a ↦ ∑ i, ∑ j, (b.repr u i * b.repr v j) * B a (b i) (b j)) := by
    funext a
    exact bilinear_apply_eq_basis_sum b (B a) u v
  rw [hf, bilinear_apply_eq_basis_sum b B₀ u v]
  exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
    (h i j).const_mul (b.repr u i * b.repr v j)

end Bilinear

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem exponential_scaled_pairing_tendsto (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun s : ℝ ↦ (s⁻¹) ^ 2 *
      pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x u v)
      (𝓝[>] (0 : ℝ)) (𝓝 (4 * inner ℝ u v)) := by
  let B := fun s : ℝ ↦ (s⁻¹) ^ 2 •
    pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (4 : ℝ) • innerSL ℝ
  have h := exponential_scaled_gram_tendsto G hmax hT hwindow x
  have hentries (i j : Fin n) :
      Tendsto (fun s ↦ B s (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) (𝓝[>] (0 : ℝ))
        (𝓝 (B₀ (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j))) := by
    change Tendsto (fun s ↦ (s⁻¹) ^ 2 *
      pullbackMetricForm (F.metric (T - s ^ 2)) (exponentialSliceChart G (s ^ 2)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) _
      (𝓝 (4 * inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)))
    rw [OrthonormalBasis.inner_eq_ite]
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j
  exact tendsto_bilinear_apply_of_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hentries u v

end PoincareConjecture.M10
