import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.TwoForm
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors

set_option autoImplicit false

open scoped BigOperators
open Matrix
open scoped Manifold ContDiff Bundle

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma hamilton_diagonal_nonneg_of_skew_quadratic_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hQ : ∀ (U : I → I → ℝ) (W : I → ℝ),
      (∀ a b, U a b = -U b a) →
      0 ≤ (∑ a, ∑ b, M a b * W a * W b) +
        2 * (∑ a, ∑ b, ∑ c, P a b c * U a b * W c) +
        (∑ a, ∑ b, ∑ c, ∑ d, R a b c d * U a b * U c d))
    (V : I → ℝ) :
    ∀ a, 0 ≤ M a a + 2 * (∑ i, P i a a * V i) +
      ∑ i, ∑ k, R i a k a * V i * V k := by
  intro a
  let e : I → ℝ := fun i => if i = a then 1 else 0
  let U : I → I → ℝ := fun i j => (V i * e j - e i * V j) / 2
  have hU : ∀ i j, U i j = -U j i := by
    intro i j
    dsimp [U]
    ring
  have h := hQ U e hU
  have hR' :
      (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * U i j * U k l) =
        ∑ i, ∑ k, R i a k a * V i * V k := by
    have hR₀ := curvature_contraction_half_wedge R hfirst hlast V e
    simpa [U, e, mul_ite, ite_mul, Finset.sum_ite_eq', Finset.mem_univ]
      using hR₀
  have hP' :
      (∑ i, ∑ j, P i j a * U i j) = ∑ i, P i a a * V i := by
    have hP₀ := skew_contraction_half_wedge (fun i j => P i j a)
      (fun i j => hP i j a) V e
    simpa [U, e, mul_ite, ite_mul, Finset.sum_ite_eq', Finset.mem_univ]
      using hP₀
  rw [hR'] at h
  have hmix :
      (∑ a_1, ∑ b, ∑ c, P a_1 b c * U a_1 b * e c) =
        ∑ i, P i a a * V i := by
    simpa [e, mul_ite, Finset.sum_ite_eq', Finset.mem_univ] using hP'
  rw [hmix] at h
  dsimp [e] at h
  simp only [mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    mul_one, mul_zero] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

lemma hamilton_diagonal_nonneg_of_block_posSemidef
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hM : ∀ a b, M a b = M b a)
    (hQ : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef)
    (V : I → ℝ) :
    ∀ a, 0 ≤ M a a + 2 * (∑ i, P i a a * V i) +
      ∑ i, ∑ k, R i a k a * V i * V k := by
  apply hamilton_diagonal_nonneg_of_skew_quadratic_nonneg R P M hfirst hlast hP
  intro U W hU
  exact hamiltonBlock_quadratic_nonneg_of_posSemidef R P M hR hM hQ U W

universe u

theorem hamilton_diagonal_nonneg_of_geometric_block
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (τ : ℝ)
    (x : M) (v : TangentSpace (𝓡 n) x)
    (hQ : let eb := (F.metric t).orthonormalBasis x
      (Matrix.fromBlocks
        (fun ac bd : (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
          (F.connection t).curvatureTensor x (eb ac.1) (eb ac.2)
            (eb bd.1) (eb bd.2))
        (fun (ac : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) d =>
          hamiltonP (F.connection t) x (eb ac.1) (eb ac.2) (eb d))
        (fun c (bd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
            Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
          hamiltonP (F.connection t) x (eb bd.1) (eb bd.2) (eb c))
        (fun a b => hamiltonM (F.connection t) τ x (eb a) (eb b))).PosSemidef) :
    ∀ a, 0 ≤ hamiltonM (F.connection t) τ x
        ((F.metric t).orthonormalBasis x a)
        ((F.metric t).orthonormalBasis x a) +
      2 * (∑ i, hamiltonP (F.connection t) x
        ((F.metric t).orthonormalBasis x i)
        ((F.metric t).orthonormalBasis x a)
        ((F.metric t).orthonormalBasis x a) *
        (F.metric t).inner x v ((F.metric t).orthonormalBasis x i)) +
      (∑ i, ∑ k, (F.connection t).curvatureTensor x
        ((F.metric t).orthonormalBasis x i)
        ((F.metric t).orthonormalBasis x a)
        ((F.metric t).orthonormalBasis x k)
        ((F.metric t).orthonormalBasis x a) *
        (F.metric t).inner x v ((F.metric t).orthonormalBasis x i) *
        (F.metric t).inner x v ((F.metric t).orthonormalBasis x k)) := by
  let g := F.metric t
  let D := F.connection t
  let eb := g.orthonormalBasis x
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let R : I → I → I → I → ℝ := fun i j k l =>
    D.curvatureTensor x (eb i) (eb j) (eb k) (eb l)
  let P : I → I → I → ℝ := fun i j k => hamiltonP D x (eb i) (eb j) (eb k)
  let M' : I → I → ℝ := fun i j => hamiltonM D τ x (eb i) (eb j)
  have hcalc := hC.tensor_calculus n M g D
  have hR : ∀ a b c d, R a b c d = R c d a b := by
    intro a b c d
    exact (hcalc.2.2.2.1 x (eb a) (eb b) (eb c) (eb d)).2.1
  have hfirst : ∀ a b c d, R a b c d = -R b a c d := by
    intro a b c d
    change D.curvatureTensor x (eb a) (eb b) (eb c) (eb d) =
      -D.curvatureTensor x (eb b) (eb a) (eb c) (eb d)
    have h₁ := (hcalc.2.2.2.1 x (eb a) (eb b) (eb c) (eb d)).2.1
    have h₂ := (hcalc.2.2.2.1 x (eb c) (eb d) (eb b) (eb a)).1
    have h₃ := (hcalc.2.2.2.1 x (eb b) (eb a) (eb c) (eb d)).2.1
    linarith
  have hlast : ∀ a b c d, R a b c d = -R a b d c := by
    intro a b c d
    have hs := hcalc.2.2.2.1 x (eb a) (eb b) (eb c) (eb d)
    change D.curvatureTensor x (eb a) (eb b) (eb c) (eb d) =
      -D.curvatureTensor x (eb a) (eb b) (eb d) (eb c)
    exact hs.1
  have hP : ∀ a b c, P a b c = -P b a c := by
    intro a b c
    exact hamiltonP_skew D x (eb a) (eb b) (eb c)
  have hM : ∀ a b, M' a b = M' b a := by
    intro a b
    exact hamiltonM_symm_of_curvatureTheory hC J F t (interior_subset ht) τ x
      (eb a) (eb b)
  have hQ' : (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M').PosSemidef := by
    simpa only [R, P, M', I, eb, g, D] using hQ
  simpa only [R, P, M', I, eb, g, D] using
    (hamilton_diagonal_nonneg_of_block_posSemidef R P M' hR hfirst hlast hP hM hQ'
      (fun i => g.inner x v (eb i)))

end Poincare.RicciFlow.Harnack
