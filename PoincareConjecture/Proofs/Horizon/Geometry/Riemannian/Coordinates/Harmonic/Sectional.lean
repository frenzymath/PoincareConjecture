import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry
import Mathlib.Analysis.InnerProductSpace.Rayleigh









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



lemma curvatureTensor_diagonal_eq_sectional_mul_gram (D : LeviCivitaData g)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v u v = D.sectionalCurvature x u v *
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_cases hgram : g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 = 0
  · rw [hgram, mul_zero]
    by_cases hv : v = 0
    · subst v
      have h := D.curvatureTensor_smul_second x (0 : ℝ) u u u 0
      simpa only [zero_smul, zero_mul] using h
    · have hvv : g.inner x v v ≠ 0 := ne_of_gt (g.pos x v hv)
      have hu : u = (g.inner x u v / g.inner x v v) • v := by
        apply sub_eq_zero.mp
        apply (inner_self_eq_zero (𝕜 := ℝ)).mp
        change g.inner x (u - (g.inner x u v / g.inner x v v) • v)
          (u - (g.inner x u v / g.inner x v v) • v) = 0
        simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, g.symm x v u]
        field_simp
        nlinarith [hgram]
      rw [hu]
      rw [D.curvatureTensor_smul_first, D.curvatureTensor_zero_first, mul_zero]
  · unfold sectionalCurvature
    exact (div_mul_cancel₀ _ hgram).symm



lemma tangentNorm_radialCurvature_le_of_sectional
    (D : LeviCivitaData g) (x : M) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u v| ≤ K)
    (v u : TangentSpace (𝓡 n) x) :
    g.tangentNorm x (D.curvature x u v v) ≤
      (K * g.tangentNorm x v ^ 2) * g.tangentNorm x u := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let A := (D.radialCurvature x v).toContinuousLinearMap
  have hsymm : A.IsSymmetric := fun a b => D.inner_radialCurvature_symm x v a b
  have hquad (w : TangentSpace (𝓡 n) x) :
      |inner ℝ (A w) w| ≤ (K * ‖v‖ ^ 2) * ‖w‖ ^ 2 := by
    have hgram : 0 ≤ g.inner x w w * g.inner x v v - (g.inner x w v) ^ 2 := by
      have h := real_inner_mul_inner_self_le w v
      change g.inner x w v * g.inner x w v ≤ g.inner x w w * g.inner x v v at h
      nlinarith
    change |D.curvatureTensor x w v w v| ≤ _
    rw [D.curvatureTensor_diagonal_eq_sectional_mul_gram, abs_mul, abs_of_nonneg hgram]
    calc
      _ ≤ K * (g.inner x w w * g.inner x v v - (g.inner x w v) ^ 2) :=
        mul_le_mul_of_nonneg_right (hsec w v) hgram
      _ ≤ K * (g.inner x w w * g.inner x v v) := by
        nlinarith [mul_nonneg hK (sq_nonneg (g.inner x w v))]
      _ = _ := by
        change K * (inner ℝ w w * inner ℝ v v) = _
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        ring
  have hnorm : ‖A‖ ≤ K * ‖v‖ ^ 2 := by
    rw [A.norm_eq_iSup_rayleighQuotient hsymm]
    apply ciSup_le
    intro w
    by_cases hw : w = 0
    · simp [hw, ContinuousLinearMap.rayleighQuotient]
      positivity
    · rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply]
      simp only [RCLike.re_to_real, abs_div, abs_of_nonneg (sq_nonneg ‖w‖)]
      exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hw))).mpr (hquad w)
  have hn (w : TangentSpace (𝓡 n) x) : g.tangentNorm x w = ‖w‖ := by
    change Real.sqrt (inner ℝ w w) = ‖w‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  simp only [hn]
  exact (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg u))



lemma three_curvatureTensor_eq_radial_polarization (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    3 * D.curvatureTensor x u v z w =
      D.curvatureTensor x u (v + w) z (v + w) -
        D.curvatureTensor x u v z v - D.curvatureTensor x u w z w -
      (D.curvatureTensor x v (u + w) z (u + w) -
        D.curvatureTensor x v u z u - D.curvatureTensor x v w z w) := by
  have h := congrArg (fun y => g.inner x y z) (D.curvature_cyclic_eq_zero x u v w)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  change D.curvatureTensor x u v z w + D.curvatureTensor x v w z u +
    D.curvatureTensor x w u z v = 0 at h
  rw [D.curvatureTensor_swap_first x w u z v] at h
  simp only [D.curvatureTensor_add_second, D.curvatureTensor_add_last]
  rw [D.curvatureTensor_swap_first x v u z w]
  linarith


lemma abs_curvatureTensor_le_four_mul_of_unit (D : LeviCivitaData g) (x : M)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u v| ≤ K)
    (u v w z : TangentSpace (𝓡 n) x)
    (hu : g.inner x u u = 1) (hv : g.inner x v v = 1)
    (hw : g.inner x w w = 1) (hz : g.inner x z z = 1) :
    |D.curvatureTensor x u v w z| ≤ 4 * K := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hn (a : TangentSpace (𝓡 n) x) : g.tangentNorm x a = ‖a‖ := by
    change Real.sqrt (inner ℝ a a) = ‖a‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg a)]
  have hunit (a : TangentSpace (𝓡 n) x) (ha : g.inner x a a = 1) : ‖a‖ = 1 := by
    change inner ℝ a a = 1 at ha
    rw [real_inner_self_eq_norm_sq] at ha
    nlinarith [norm_nonneg a]
  have hu' := hunit u hu
  have hv' := hunit v hv
  have hw' := hunit w hw
  have hz' := hunit z hz
  have hrad (a b c : TangentSpace (𝓡 n) x) (ha : ‖a‖ = 1) (hc : ‖c‖ = 1) :
      |D.curvatureTensor x a b c b| ≤ K * ‖b‖ ^ 2 := by
    have h := D.tangentNorm_radialCurvature_le_of_sectional x hK hsec b a
    simp only [hn, ha, mul_one] at h
    have hi := abs_real_inner_le_norm (D.curvature x a b b) c
    change |D.curvatureTensor x a b c b| ≤ _ at hi
    simpa only [hc, mul_one] using hi.trans (mul_le_mul_of_nonneg_right h (norm_nonneg c))
  have hsum (a b c d : TangentSpace (𝓡 n) x)
      (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) :
      |D.curvatureTensor x a (b + d) c (b + d) -
        D.curvatureTensor x a b c b - D.curvatureTensor x a d c d| ≤ 6 * K := by
    have hbd : ‖b + d‖ ≤ 2 := by
      have h := norm_add_le b d
      rw [hb, hd] at h
      norm_num at h
      exact h
    have hsq : ‖b + d‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (b + d)]
    calc
      _ ≤ |D.curvatureTensor x a (b + d) c (b + d)| +
          |D.curvatureTensor x a b c b| + |D.curvatureTensor x a d c d| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * ‖b + d‖ ^ 2 + K * ‖b‖ ^ 2 + K * ‖d‖ ^ 2 :=
        add_le_add (add_le_add (hrad a (b + d) c ha hc) (hrad a b c ha hc))
          (hrad a d c ha hc)
      _ ≤ 6 * K := by rw [hb, hd]; nlinarith [mul_le_mul_of_nonneg_left hsq hK]
  have hp := congrArg abs (D.three_curvatureTensor_eq_radial_polarization x u v z w)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at hp
  have hab := abs_sub
    (D.curvatureTensor x u (v + z) w (v + z) -
      D.curvatureTensor x u v w v - D.curvatureTensor x u z w z)
    (D.curvatureTensor x v (u + z) w (u + z) -
      D.curvatureTensor x v u w u - D.curvatureTensor x v z w z)
  rw [← hp] at hab
  have h1 := hsum u v w z hu' hv' hw' hz'
  have h2 := hsum v u w z hv' hu' hw' hz'
  linarith



lemma curvatureTensorNorm_le_of_sectional (D : LeviCivitaData g) (x : M)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ u v : TangentSpace (𝓡 n) x, |D.sectionalCurvature x u v| ≤ K) :
    D.curvatureTensorNorm x ≤ 4 * (n : ℝ) ^ 2 * K := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hterm (i j k l) : (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 ≤ (4 * K) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
      (D.abs_curvatureTensor_le_four_mul_of_unit x hK hsec _ _ _ _ (hb i) (hb j) (hb k) (hb l))
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, (4 * K) ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm i j k l
    _ = (4 * (n : ℝ) ^ 2 * K) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring

end PoincareConjecture.LeviCivitaData
