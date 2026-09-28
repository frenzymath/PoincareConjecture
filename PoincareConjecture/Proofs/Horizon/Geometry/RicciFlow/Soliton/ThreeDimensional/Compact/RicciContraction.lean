import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Pinching.CurvatureTensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction













set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

private theorem cyclic_pair_eq
    (f g : Fin 3 → Fin 3 → ℝ)
    (hf : ∀ a b, f a b = -f b a) (hg : ∀ a b, g a b = -g b a)
    (h : ∀ i, f (i + 1) (i + 2) = g (i + 1) (i + 2)) (a b : Fin 3) :
    f a b = g a b := by
  have h12 : f 1 2 = g 1 2 := h 0
  have h20 : f 2 0 = g 2 0 := h 1
  have h01 : f 0 1 = g 0 1 := h 2
  fin_cases a <;> fin_cases b
  · change f 0 0 = g 0 0
    linarith only [hf 0 0, hg 0 0]
  · exact h01
  · change f 0 2 = g 0 2
    linarith only [hf 0 2, hg 0 2, h20]
  · change f 1 0 = g 1 0
    linarith only [hf 1 0, hg 1 0, h01]
  · change f 1 1 = g 1 1
    linarith only [hf 1 1, hg 1 1]
  · exact h12
  · exact h20
  · change f 2 1 = g 2 1
    linarith only [hf 2 1, hg 2 1, h12]
  · change f 2 2 = g 2 2
    linarith only [hf 2 2, hg 2 2]

private theorem frame_curvature_reconstruction
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j) (i j k l : Fin 3) :
    let C := fun a b => ∑ p, R a p b p
    R i j k l =
      (if i = k then C j l else 0) + (if j = l then C i k else 0) -
      (if i = l then C j k else 0) - (if j = k then C i l else 0) -
      ((∑ a, C a a) / 2) *
        ((if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0)) := by
  let C := fun a b => ∑ p, R a p b p
  let S := fun i j k l : Fin 3 =>
    (if i = k then C j l else 0) + (if j = l then C i k else 0) -
      (if i = l then C j k else 0) - (if j = k then C i l else 0) -
      ((∑ a, C a a) / 2) *
        ((if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0))
  change R i j k l = S i j k l
  have hSfirst (i j k l) : S i j k l = -S j i k l := by
    simp only [S, and_comm]
    ring
  have hSlast (i j k l) : S i j k l = -S i j l k := by
    simp only [S]
    ring
  apply cyclic_pair_eq (fun i j => R i j k l) (fun i j => S i j k l)
    (fun i j => hfirst i j k l) (fun i j => hSfirst i j k l)
  intro a
  apply cyclic_pair_eq _ _ (hlast (a + 1) (a + 2)) (hSlast (a + 1) (a + 2))
  intro b
  have hzero₁ (i k l) : R i i k l = 0 := by linarith [hfirst i i k l]
  have hzero₂ (i j k) : R i j k k = 0 := by linarith [hlast i j k k]
  have h10 k l := hfirst 1 0 k l
  have h20 k l := hfirst 2 0 k l
  have h21 k l := hfirst 2 1 k l
  have h10' i j := hlast i j 1 0
  have h20' i j := hlast i j 2 0
  have h21' i j := hlast i j 2 1
  have hp₁ := hpair 0 2 0 1
  have hp₂ := hpair 1 2 0 1
  have hp₃ := hpair 1 2 0 2
  fin_cases a <;> fin_cases b <;>
    simp +decide [S, C, Fin.sum_univ_succ, hzero₁, hzero₂,
      h10, h20, h21, h10', h20', h21', hp₁, hp₂, hp₃] <;>
    ring

private theorem frame_curvature_ricci_contraction
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j) :
    let C := fun a b => ∑ p, R a p b p
    let scalar := ∑ a, C a a
    let normSq := ∑ a, ∑ b, (C a b) ^ 2
    (∑ i, ∑ j, C i j * (∑ a, ∑ b, R i a j b * C a b)) =
      (5 / 2 : ℝ) * scalar * normSq - (1 / 2 : ℝ) * scalar ^ 3 -
        2 * (∑ i, ∑ j, ∑ k, C i j * C j k * C k i) := by
  let C := fun a b => ∑ p, R a p b p
  have hC (i j) : C i j = C j i := by
    apply Finset.sum_congr rfl
    intro k _
    exact hpair i k j k
  have hrec (i j k l) : R i j k l =
      (if i = k then C j l else 0) + (if j = l then C i k else 0) -
      (if i = l then C j k else 0) - (if j = k then C i l else 0) -
      ((∑ a, C a a) / 2) *
        ((if i = k ∧ j = l then 1 else 0) - (if i = l ∧ j = k then 1 else 0)) :=
    frame_curvature_reconstruction R hfirst hlast hpair i j k l
  change (∑ i, ∑ j, C i j * (∑ a, ∑ b, R i a j b * C a b)) = _
  simp_rw [hrec]
  have h10 := hC 1 0
  have h20 := hC 2 0
  have h21 := hC 2 1
  simp +decide [Fin.sum_univ_succ, h10, h20, h21]
  ring

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] {g : RiemannianMetric 3 M}



theorem curvature_ricci_contraction_eq_cubic
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    let b := g.orthonormalBasis x
    (∑ i, ∑ j, D.ricci x (b i) (b j) * (∑ a, ∑ c,
      D.curvatureTensor x (b i) (b a) (b j) (b c) * D.ricci x (b a) (b c))) =
      (5 / 2 : ℝ) * D.scalarCurvature x * D.ricciNormSq x -
        (1 / 2 : ℝ) * D.scalarCurvature x ^ 3 -
        2 * (∑ i, ∑ j, ∑ k,
          D.ricci x (b i) (b j) * D.ricci x (b j) (b k) * D.ricci x (b k) (b i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let b := (g.orthonormalBasis x).reindex (finCongr hd)
  let R := fun i j k l : Fin 3 => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have hfirst (i j k l) : R i j k l = -R j i k l := by
    dsimp only [R]
    rw [(hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1,
      (hD.2.2.2.1 x (b k) (b l) (b i) (b j)).1,
      (hD.2.2.2.1 x (b k) (b l) (b j) (b i)).2.1]
  have hlast (i j k l) : R i j k l = -R i j l k :=
    (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).1
  have hpair (i j k l) : R i j k l = R k l i j :=
    (hD.2.2.2.1 x (b i) (b j) (b k) (b l)).2.1
  have hric (i j) : (∑ p, R i p j p) = D.ricci x (b i) (b j) :=
    (D.ricci_eq_sum_orthonormalBasis hD x b (b i) (b j)).symm
  have h := frame_curvature_ricci_contraction R hfirst hlast hpair
  dsimp only at h
  simp_rw [hric] at h
  simpa only [R, b, OrthonormalBasis.reindex_apply,
    ← Equiv.sum_comp (finCongr hd).symm, scalarCurvature, ricciNormSq] using h

end PoincareConjecture.LeviCivitaData
