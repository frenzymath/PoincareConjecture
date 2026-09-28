import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.TwoForm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Manifold ContDiff Bundle

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]



lemma sum_sq_half_wedge_le (A W : I → ℝ) :
    (∑ a, ∑ b, ((A a * W b - W a * A b) / 2) ^ 2) ≤
      (∑ a, (A a) ^ 2) * ∑ b, (W b) ^ 2 := by
  calc
    _ ≤ ∑ a : I, ∑ b : I, ((A a) ^ 2 * (W b) ^ 2 + (W a) ^ 2 * (A b) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      nlinarith only [sq_nonneg (A a * W b + W a * A b)]
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

variable [DecidableEq I]



lemma sum_sq_prescribed_jet_le
    (Ric : I → I → ℝ) (W : I → ℝ) (C k : ℝ)
    (hC : 0 ≤ C) (hRic : ∀ e a, |Ric e a| ≤ C) :
    (∑ e, ∑ a, ∑ b,
      (((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) ^ 2) ≤
      (2 * (Fintype.card I : ℝ) ^ 2 * C ^ 2 +
        2 * Fintype.card I * k ^ 2) * ∑ a, (W a) ^ 2 := by
  have hW : 0 ≤ ∑ a, (W a) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hentry (e a : I) :
      (Ric e a + k * (if e = a then 1 else 0)) ^ 2 ≤
        2 * C ^ 2 + 2 * k ^ 2 * (if e = a then 1 else 0) := by
    have hsq : (Ric e a) ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hRic e a)
    by_cases h : e = a
    · subst a
      simp only [if_true, mul_one]
      nlinarith only [hsq, sq_nonneg (Ric e e - k)]
    · simp only [h, if_false, mul_zero, add_zero]
      nlinarith only [hsq, sq_nonneg C]
  calc
    _ ≤ ∑ e, (∑ a, (Ric e a + k * (if e = a then 1 else 0)) ^ 2) *
        ∑ a, (W a) ^ 2 := by
      exact Finset.sum_le_sum (fun e _ =>
        sum_sq_half_wedge_le (fun a => Ric e a + k * (if e = a then 1 else 0)) W)
    _ = (∑ e, ∑ a, (Ric e a + k * (if e = a then 1 else 0)) ^ 2) *
        ∑ a, (W a) ^ 2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ e : I, ∑ a : I, (2 * C ^ 2 + 2 * k ^ 2 * (if e = a then 1 else 0))) *
        ∑ a, (W a) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hW
      exact Finset.sum_le_sum (fun e _ => Finset.sum_le_sum (fun a _ => hentry e a))
    _ = _ := by
      simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

universe u

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma sum_sq_geometric_prescribed_jet_le
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (K k : ℝ) (hK : 0 ≤ K) (hcurv : D.curvatureDerivativeNorm 0 x ≤ K)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let b := g.orthonormalBasis x
    let Ric := fun e a => D.ricci x (b e) (b a)
    (∑ e, ∑ a, ∑ b,
      (((Ric e a + k * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) ^ 2) ≤
      (2 * (n : ℝ) ^ 4 * K ^ 2 + 2 * n * k ^ 2) * ∑ a, (W a) ^ 2 := by
  classical
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.tangentNorm x (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hRic (e a : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      |D.ricci x (b e) (b a)| ≤ (n : ℝ) * K := by
    have h := D.abs_ricci_le_curvatureDerivativeNorm_zero hD x (b e) (b a)
    simp only [hb, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hcurv (Nat.cast_nonneg n))
  have h := sum_sq_prescribed_jet_le (fun e a => D.ricci x (b e) (b a))
    W ((n : ℝ) * K) k (mul_nonneg (Nat.cast_nonneg n) hK) hRic
  simp only [Fintype.card_fin, hdim] at h
  convert h using 1
  ring



lemma neg_mul_sum_sq_geometric_prescribed_jet_ge
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (K k ψ : ℝ) (hK : 0 ≤ K) (hcurv : D.curvatureDerivativeNorm 0 x ≤ K)
    (hψ : 0 ≤ ψ)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let b := g.orthonormalBasis x
    let Ric := fun e a => D.ricci x (b e) (b a);
    -(4 * (n : ℝ) ^ 4 * K ^ 2 + 4 * n * k ^ 2) * ψ * (∑ a, (W a) ^ 2) ≤
      -2 * ψ * (∑ e, ∑ a, ∑ b,
        (((Ric e a + k * (if e = a then 1 else 0)) * W b -
          W a * (Ric e b + k * (if e = b then 1 else 0))) / 2) ^ 2) := by
  dsimp only
  have h := mul_le_mul_of_nonpos_left
    (sum_sq_geometric_prescribed_jet_le D hD x K k hK hcurv W)
    (show -2 * ψ ≤ 0 by linarith)
  convert h using 1
  · rfl
  · ring



lemma sum_sq_geometric_prescribed_jet_le_time_bound
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (K τ T : ℝ) (hK : 0 ≤ K) (hcurv : D.curvatureDerivativeNorm 0 x ≤ K)
    (hτ : 0 < τ) (hT : τ ≤ T)
    (W : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) :
    let b := g.orthonormalBasis x
    let Ric := fun e a => D.ricci x (b e) (b a)
    (∑ e, ∑ a, ∑ b,
      (((Ric e a + (1 / (2 * τ)) * (if e = a then 1 else 0)) * W b -
        W a * (Ric e b + (1 / (2 * τ)) * (if e = b then 1 else 0))) / 2) ^ 2) ≤
      (2 * (n : ℝ) ^ 4 * K ^ 2 * T ^ 2 + n / 2) / τ ^ 2 * ∑ a, (W a) ^ 2 := by
  have hτsq : τ ^ 2 ≤ T ^ 2 := (sq_le_sq₀ hτ.le (hτ.le.trans hT)).2 hT
  have hcoeff : 2 * (n : ℝ) ^ 4 * K ^ 2 + 2 * n * (1 / (2 * τ)) ^ 2 ≤
      (2 * (n : ℝ) ^ 4 * K ^ 2 * T ^ 2 + n / 2) / τ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).2
    calc
      _ = 2 * (n : ℝ) ^ 4 * K ^ 2 * τ ^ 2 + n / 2 := by
        field_simp
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left hτsq
          (show 0 ≤ 2 * (n : ℝ) ^ 4 * K ^ 2 by positivity)
        linarith only [h]
  exact (sum_sq_geometric_prescribed_jet_le D hD x K (1 / (2 * τ)) hK hcurv W).trans
    (mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end Poincare.RicciFlow.Harnack
