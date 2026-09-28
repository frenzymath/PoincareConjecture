import PoincareConjecture.Proofs.Ch01.Koszul
import PoincareConjecture.Proofs.M03.Existence.ChartJetSource
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle BigOperators
open Matrix

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def frameMetricJet (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    MetricJet2 (n := n) where
  value i j := g.inner x (F i x) (F j x)
  first a i j :=
    mvfderiv (𝓡 n) (fun y => g.inner y (F i y) (F j y)) x (F a x)
  second a b i j :=
    mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n)
        (fun z => g.inner z (F i z) (F j z)) y (F b y)) x (F a x)

theorem frameMetricJet_first_symm (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x)
    (x : M) (a i j : Fin n) :
    (frameMetricJet g F x).first a i j =
      (frameMetricJet g F x).first a j i := by
  exact congrArg (fun f : M → ℝ => mvfderiv (𝓡 n) f x (F a x))
    (funext fun y => g.symm y (F i y) (F j y))

theorem frameMetricJet_value_posDef (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x)
    (x : M) (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hF : ∀ i, F i x = b i) :
    (frameMetricJet g F x).value.PosDef := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgram : (frameMetricJet g F x).value = Matrix.gram ℝ b := by
    ext i j
    change g.inner x (F i x) (F j x) = g.inner x (b i) (b j)
    rw [hF i, hF j]
  rw [hgram]
  exact Matrix.posDef_gram_of_linearIndependent b.linearIndependent

theorem connection_repr_eq_christoffelJet
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x)
    {x : M} (b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x))
    (hF : ∀ a, F a x = b a)
    (hregular : ∀ a, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (F a)) x)
    (hbracket : ∀ a c, VectorField.mlieBracket (𝓡 n) (F a) (F c) x = 0)
    (k i j : Fin n) :
    b.repr (D.connection (F j) x (F i x)) k =
      christoffelJet (frameMetricJet g F x) k i j := by
  classical
  let G := (frameMetricJet g F x).value
  let V := D.connection (F j) x (F i x)
  let A : Fin n → ℝ := fun r => b.repr V r
  let P : Fin n → ℝ := fun l =>
    (frameMetricJet g F x).first i l j +
      (frameMetricJet g F x).first j l i -
      (frameMetricJet g F x).first l i j
  have hpair (l : Fin n) :
      g.inner x V (F l x) = ∑ r, G l r * A r := by
    calc
      g.inner x V (F l x) =
          g.inner x (∑ r, b.repr V r • b r) (b l) := by
        rw [b.sum_repr V, hF l]
      _ = ∑ r, G l r * A r := by
        simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro r _
        dsimp [G, A, frameMetricJet]
        rw [hF l, hF r, g.symm x (b r) (b l)]
        ring
  have hkoszul (l : Fin n) : 2 * g.inner x V (F l x) = P l := by
    have h := D.koszul (F i) (F j) (F l)
      (hregular i) (hregular j) (hregular l)
    rw [hbracket i j, hbracket i l, hbracket j l] at h
    simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero, sub_zero] at h
    change 2 * g.inner x V (F l x) =
      (frameMetricJet g F x).first i j l +
        (frameMetricJet g F x).first j l i -
        (frameMetricJet g F x).first l i j at h
    rw [frameMetricJet_first_symm g F x i j l] at h
    exact h
  have hmatrix : G *ᵥ A = fun l => (1 / 2 : ℝ) * P l := by
    funext l
    change (∑ r, G l r * A r) = (1 / 2 : ℝ) * P l
    rw [← hpair l]
    linarith only [hkoszul l]
  have hpos : G.PosDef := frameMetricJet_value_posDef g F x b hF
  have hinverse : G⁻¹ *ᵥ (G *ᵥ A) = A := by
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)),
      Matrix.one_mulVec]
  change A k = christoffelJet (frameMetricJet g F x) k i j
  calc
    A k = (G⁻¹ *ᵥ (G *ᵥ A)) k := (congrFun hinverse k).symm
    _ = (∑ l, G⁻¹ k l * ((1 / 2 : ℝ) * P l)) := by
      rw [hmatrix]
      rfl
    _ = christoffelJet (frameMetricJet g F x) k i j := by
      change (∑ l, G⁻¹ k l * ((1 / 2 : ℝ) * P l)) =
        (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * P l
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

end PoincareConjecture.DeTurckNative

end
