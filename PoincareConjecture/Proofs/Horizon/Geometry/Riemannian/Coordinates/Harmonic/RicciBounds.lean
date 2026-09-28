import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Ricci








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

namespace RiemannianMetric

private lemma inner_sq_le {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (g.inner x u v) ^ 2 ≤ g.inner x u u * g.inner x v v := by
  let : InnerProductSpace.Core ℝ (TangentSpace (𝓡 n) x) :=
    g.toRiemannianMetric.toCore x
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) u v
  change ‖g.inner x u v‖ * ‖g.inner x v u‖ ≤ g.inner x u u * g.inner x v v at h
  rw [g.symm x v u, ← norm_mul, Real.norm_eq_abs, abs_mul_self] at h
  simpa only [pow_two] using h

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))



lemma fderiv_inverse_apply (x u : EuclideanSpace ℝ (Fin n))
    (ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    fderiv ℝ (fun y ↦ (g.euclideanCoefficients y).inverse ξ) x u =
      -(g.euclideanCoefficients x).inverse
        (fderiv ℝ g.euclideanCoefficients x u ((g.euclideanCoefficients x).inverse ξ)) := by
  have hinv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hG := (g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)
  have hI : DifferentiableAt ℝ (fun y ↦ (g.euclideanCoefficients y).inverse ξ) x :=
    ((hinv.contDiffAt_map_inverse.comp x
      (g.contDiffAt_euclideanCoefficients x)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have heq : (fun y ↦ g.euclideanCoefficients y ((g.euclideanCoefficients y).inverse ξ)) =
      (fun _ ↦ ξ) := funext fun y ↦ (g.inner_isInvertible y).self_apply_inverse ξ
  have hd := congrArg (fun f : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    ↦ fderiv ℝ f x u) heq
  rw [(hG.hasFDerivAt.clm_apply hI.hasFDerivAt).fderiv] at hd
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply] at hd
  have h := congrArg (g.euclideanCoefficients x).inverse hd
  rw [map_add, hinv.inverse_apply_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h


lemma fderiv_inverseCoefficients_eq (x u : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x u =
      -EuclideanSpace.proj j ((g.euclideanCoefficients x).inverse
        (fderiv ℝ g.euclideanCoefficients x u
          ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i)))) := by
  have hinv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hI : DifferentiableAt ℝ
      (fun y ↦ (g.euclideanCoefficients y).inverse (EuclideanSpace.proj i)) x :=
    ((hinv.contDiffAt_map_inverse.comp x
      (g.contDiffAt_euclideanCoefficients x)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x hI.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x = _ at h
  rw [h, ContinuousLinearMap.comp_apply, g.fderiv_inverse_apply, map_neg]

private lemma norm_proj (i : Fin n) : ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ = 1 := by
  have h : EuclideanSpace.proj (𝕜 := ℝ) i =
      innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    ext v
    simp only [PiLp.proj_apply, innerSL_apply_apply, EuclideanSpace.basisFun_inner]
  rw [h, innerSL_apply_norm, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one]



lemma abs_fderiv_inverseCoefficients_le (x u : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    |fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x u| ≤
      ‖(g.euclideanCoefficients x).inverse‖ ^ 2 *
        ‖fderiv ℝ g.euclideanCoefficients x‖ * ‖u‖ := by
  rw [g.fderiv_inverseCoefficients_eq, abs_neg, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖EuclideanSpace.proj (𝕜 := ℝ) j‖ *
        (‖(g.euclideanCoefficients x).inverse‖ *
          (‖fderiv ℝ g.euclideanCoefficients x‖ * ‖u‖ *
            (‖(g.euclideanCoefficients x).inverse‖ * ‖EuclideanSpace.proj (𝕜 := ℝ) i‖))) := by
      apply (EuclideanSpace.proj (𝕜 := ℝ) j).le_opNorm _ |>.trans
      gcongr
      apply (g.euclideanCoefficients x).inverse.le_opNorm _ |>.trans
      gcongr
      exact ((fderiv ℝ g.euclideanCoefficients x).le_opNorm₂ u _).trans
        (mul_le_mul_of_nonneg_left ((g.euclideanCoefficients x).inverse.le_opNorm _)
          (by positivity))
    _ = _ := by rw [norm_proj, norm_proj]; ring


lemma abs_inverseCoefficients_le_opNorm (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    |g.inverseCoefficients x i j| ≤ ‖(g.euclideanCoefficients x).inverse‖ := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) j).le_opNorm
    ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj i))
  rw [norm_proj, one_mul] at h
  have hi := (g.euclideanCoefficients x).inverse.le_opNorm (EuclideanSpace.proj i)
  rw [norm_proj, mul_one] at hi
  exact h.trans hi


lemma norm_euclideanCoefficients_le_of_upper (x : EuclideanSpace ℝ (Fin n))
    {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2) :
    ‖g.euclideanCoefficients x‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hb
  intro u v
  have hcs := inner_sq_le g x u v
  have hpos : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hprod := mul_le_mul (hupper u) (hupper v) hpos (by positivity)
  have hbound : |g.inner x u v| ≤ b * ‖u‖ * ‖v‖ := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [hcs.trans hprod]
  exact hbound

end RiemannianMetric

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private lemma norm_euclideanConnection_le (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    ‖D.euclideanConnection u v x‖ ≤
      (2 * ‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ g.euclideanCoefficients x‖) *
        ‖u‖ * ‖v‖ := by
  rw [euclideanConnection, D.connection_const_eq_inverse]
  calc
    _ ≤ ‖(g.euclideanCoefficients x).inverse‖ *
        ‖metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) u v‖ :=
      (g.euclideanCoefficients x).inverse.le_opNorm _
    _ ≤ ‖(g.euclideanCoefficients x).inverse‖ *
        ((3 / 2 : ℝ) * ‖fderiv ℝ g.euclideanCoefficients x‖ * ‖u‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (CoordinateExponential.norm_metricKoszulCovector_le _ u v)
        (norm_nonneg _)
    _ ≤ _ := by
      have h : 0 ≤ ‖(g.euclideanCoefficients x).inverse‖ *
          ‖fderiv ℝ g.euclideanCoefficients x‖ * ‖u‖ * ‖v‖ := by positivity
      nlinarith

private lemma abs_three_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    |A u v w| ≤ ‖A‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  exact ((A u v).le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (A.le_opNorm₂ u v) (norm_nonneg w))

private lemma abs_neg_add_add_sub_le (a b c d : ℝ) :
    |-a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  calc
    _ ≤ |-a + b + c| + |d| := abs_sub _ _
    _ ≤ (|-a + b| + |c|) + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a| + |b| + |c|) + |d| := by
      gcongr
      simpa only [abs_neg] using abs_add_le (-a) b



theorem abs_harmonicRicciQuadratic_le_opNorm (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    |D.harmonicRicciQuadratic x u v| ≤
      (n : ℝ) ^ 2 *
        (4 * ‖(g.euclideanCoefficients x).inverse‖ ^ 2 +
          10 * ‖g.euclideanCoefficients x‖ * ‖(g.euclideanCoefficients x).inverse‖ ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖ := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let I := ‖(g.euclideanCoefficients x).inverse‖
  let B := ‖g.euclideanCoefficients x‖
  let G := ‖fderiv ℝ g.euclideanCoefficients x‖
  let c := 2 * I * G
  have hI : 0 ≤ I := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hc : 0 ≤ c := by positivity
  have he (i : Fin n) : ‖e i‖ = 1 := e.norm_eq_one i
  have hconn (a b : EuclideanSpace ℝ (Fin n)) :
      ‖D.euclideanConnection a b x‖ ≤ c * ‖a‖ * ‖b‖ :=
    D.norm_euclideanConnection_le x a b
  have hmetric (a b : EuclideanSpace ℝ (Fin n)) :
      |g.inner x a b| ≤ B * ‖a‖ * ‖b‖ :=
    (g.euclideanCoefficients x).le_opNorm₂ a b
  have hderiv (a b d : EuclideanSpace ℝ (Fin n)) :
      |fderiv ℝ g.euclideanCoefficients x a b d| ≤ G * ‖a‖ * ‖b‖ * ‖d‖ :=
    abs_three_apply_le _ a b d
  let F (i j : Fin n) :=
    -fderiv ℝ g.euclideanCoefficients x u (D.euclideanConnection (e i) (e j) x) v +
      fderiv ℝ g.euclideanCoefficients x (e i) (D.euclideanConnection u (e j) x) v +
      g.inner x (D.euclideanConnection u (D.euclideanConnection (e i) (e j) x) x) v -
      g.inner x (D.euclideanConnection (e i) (D.euclideanConnection u (e j) x) x) v
  have hF (i j : Fin n) : |F i j| ≤
      (2 * G * c + 2 * B * c ^ 2) * ‖u‖ * ‖v‖ := by
    have h1 : |fderiv ℝ g.euclideanCoefficients x u (D.euclideanConnection (e i) (e j) x) v| ≤
        G * ‖u‖ * c * ‖v‖ := by
      apply (hderiv _ _ _).trans
      gcongr
      simpa only [he, mul_one] using hconn (e i) (e j)
    have h2 : |fderiv ℝ g.euclideanCoefficients x (e i) (D.euclideanConnection u (e j) x) v| ≤
        G * (c * ‖u‖) * ‖v‖ := by
      apply (hderiv _ _ _).trans
      rw [he, mul_one]
      gcongr
      simpa only [he, mul_one] using hconn u (e j)
    have h3 : |g.inner x (D.euclideanConnection u (D.euclideanConnection (e i) (e j) x) x) v| ≤
        B * (c * ‖u‖ * c) * ‖v‖ := by
      apply (hmetric _ _).trans
      gcongr
      apply (hconn _ _).trans
      gcongr
      simpa only [he, mul_one] using hconn (e i) (e j)
    have h4 : |g.inner x (D.euclideanConnection (e i) (D.euclideanConnection u (e j) x) x) v| ≤
        B * (c * (c * ‖u‖)) * ‖v‖ := by
      apply (hmetric _ _).trans
      gcongr
      apply (hconn _ _).trans
      rw [he, mul_one]
      gcongr
      simpa only [he, mul_one] using hconn u (e j)
    exact (abs_neg_add_add_sub_le _ _ _ _).trans (by nlinarith [h1, h2, h3, h4])
  let J (a b : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :=
    fderiv ℝ (fun y ↦ g.inverseCoefficients y i j) x a *
      g.inner x (D.euclideanConnection (e i) (e j) x) b
  have hJ (a b : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
      |J a b i j| ≤ I ^ 2 * G * ‖a‖ * (B * c * ‖b‖) := by
    dsimp only [J]
    rw [abs_mul]
    apply mul_le_mul (g.abs_fderiv_inverseCoefficients_le x a i j) ?_
      (abs_nonneg _) (by positivity)
    apply (hmetric _ _).trans
    gcongr
    simpa only [he, mul_one] using hconn (e i) (e j)
  have hsumF : |∑ i, ∑ j, g.inverseCoefficients x i j * F i j| ≤
      (n : ℝ) ^ 2 * I * (2 * G * c + 2 * B * c ^ 2) * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ∑ i, ∑ j, |g.inverseCoefficients x i j * F i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
          Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, I * ((2 * G * c + 2 * B * c ^ 2) * ‖u‖ * ‖v‖) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (g.abs_inverseCoefficients_le_opNorm x i j) (hF i j)
          (abs_nonneg _) hI
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsumJ : |∑ i, ∑ j, (J u v i j + J v u i j)| ≤
      (n : ℝ) ^ 2 * (2 * I ^ 2 * G * B * c) * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ∑ i, ∑ j, |J u v i j + J v u i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
          Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (2 * I ^ 2 * G * B * c) * ‖u‖ * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (abs_add_le _ _).trans (by nlinarith [hJ u v i j, hJ v u i j])
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  change |(∑ i, ∑ j, g.inverseCoefficients x i j * F i j) -
    (2⁻¹ : ℝ) * (∑ i, ∑ j, (J u v i j + J v u i j))| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have h := add_le_add hsumF (mul_le_mul_of_nonneg_left hsumJ
    (by norm_num : (0 : ℝ) ≤ 2⁻¹))
  convert h using 1
  dsimp [I, B, G, c]
  ring



theorem abs_harmonicRicciQuadratic_le_of_ellipticity (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) {a b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (u v : EuclideanSpace ℝ (Fin n)) :
    |D.harmonicRicciQuadratic x u v| ≤
      (16 * (n : ℝ) ^ 2 * b / a ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖ := by
  have hb0 : 0 ≤ b := le_trans zero_le_one hb
  have hI : ‖(g.euclideanCoefficients x).inverse‖ ≤ 1 / a :=
    CoordinateExponential.norm_inverse_le_of_ellipticity ha hlower
  have hB := g.norm_euclideanCoefficients_le_of_upper x hb0 hupper
  have hc : 4 * (1 / a) ^ 2 + 10 * b * (1 / a) ^ 3 ≤ 16 * b / a ^ 3 := by
    calc
      _ = (4 * a + 10 * b) / a ^ 3 := by field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hab : a ≤ b := ha1.trans hb
        linarith
  calc
    _ ≤ (n : ℝ) ^ 2 *
        (4 * ‖(g.euclideanCoefficients x).inverse‖ ^ 2 +
          10 * ‖g.euclideanCoefficients x‖ * ‖(g.euclideanCoefficients x).inverse‖ ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖ :=
      D.abs_harmonicRicciQuadratic_le_opNorm x u v
    _ ≤ (n : ℝ) ^ 2 * (4 * (1 / a) ^ 2 + 10 * b * (1 / a) ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖ := by gcongr
    _ ≤ (n : ℝ) ^ 2 * (16 * b / a ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖ := by gcongr
    _ = _ := by ring

end LeviCivitaData

end PoincareConjecture
