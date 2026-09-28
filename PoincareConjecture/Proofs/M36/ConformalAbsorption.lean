import PoincareConjecture.Proofs.M36.ConformalPinching
import PoincareConjecture.Proofs.M36.ConformalScalar
import PoincareConjecture.Proofs.M36.ProfileBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M36

theorem smoothProfile_absorption_derivatives {C q epsilon s : ℝ}
    (hC : 0 < C) (hq : 8 ≤ q) (hepsilon : 0 < epsilon)
    (hs : 0 < s) (hs2 : s ≤ 2) :
    let f := smoothProfile C q epsilon s
    let p := deriv (smoothProfile C q epsilon) s
    let t := deriv (deriv (smoothProfile C q epsilon)) s
    0 < f ∧ 0 ≤ p ∧ 0 < t ∧ q * p ≤ 8 * t ∧
      p ^ 2 ≤ 2 * C * epsilon * t ∧ q ^ 2 * f ≤ 32 * t ∧
      q ^ 2 * t ≤ 24 * C * epsilon ∧
      (1 ≤ s → C * q ^ 2 * Real.exp (-q) * epsilon ≤ 32 * t) := by
  let f := smoothProfile C q epsilon s
  let p := deriv (smoothProfile C q epsilon) s
  let t := deriv (deriv (smoothProfile C q epsilon)) s
  have hq0 : 0 < q := by linarith only [hq]
  have hf : 0 < f := smoothProfile_pos hC hq0 hepsilon hs
  have hpf : p = q / s ^ 2 * f := smoothProfile_deriv hq0 s
  have htf : t = (q ^ 2 / s ^ 4 - 2 * q / s ^ 3) * f :=
    smoothProfile_second_deriv hq0 s
  have hs4 : 0 < s ^ 4 := pow_pos hs _
  have hsquare : s ^ 2 ≤ 4 := by
    nlinarith only [mul_self_le_mul_self hs.le hs2]
  have hfourth : s ^ 4 ≤ 16 := by
    nlinarith only [mul_self_le_mul_self (sq_nonneg s) hsquare]
  have hp : 0 ≤ p := by rw [hpf]; positivity
  have htraw : t * s ^ 4 = (q ^ 2 - 2 * q * s) * f := by
    rw [htf]
    field_simp [hs.ne']
  have htlower : q ^ 2 * f ≤ 2 * t * s ^ 4 := by
    have hco : 0 ≤ q * (q - 4 * s) :=
      mul_nonneg hq0.le (by linarith only [hq, hs2])
    nlinarith only [htraw, mul_nonneg hco hf.le]
  have ht : 0 < t := by
    have hpos : 0 < 2 * t * s ^ 4 :=
      (mul_pos (sq_pos_of_pos hq0) hf).trans_le htlower
    have hpos' := (mul_pos_iff_of_pos_right hs4).mp hpos
    linarith only [hpos']
  have hp4 : q * p * s ^ 4 = q ^ 2 * f * s ^ 2 := by
    rw [hpf]
    field_simp [hs.ne']
  have hqp : q * p ≤ 8 * t := by
    apply (mul_le_mul_iff_of_pos_right hs4).mp
    rw [hp4]
    have h := mul_le_mul_of_nonneg_left hsquare (mul_nonneg (sq_nonneg q) hf.le)
    nlinarith only [h, htlower]
  have hfexp : f = C * epsilon * Real.exp (-q / s) := smoothProfile_eq_exp hq0 hs
  have hfupper : f ≤ C * epsilon := by
    rw [hfexp]
    apply mul_le_of_le_one_right (mul_pos hC hepsilon).le
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq0.le) hs.le
  have hpsq4 : p ^ 2 * s ^ 4 = q ^ 2 * f ^ 2 := by
    rw [hpf]
    field_simp [hs.ne']
  have hpsq : p ^ 2 ≤ 2 * C * epsilon * t := by
    apply (mul_le_mul_iff_of_pos_right hs4).mp
    rw [hpsq4]
    have hf2 := mul_le_mul_of_nonneg_right hfupper hf.le
    have h1 := mul_le_mul_of_nonneg_left hf2 (sq_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left htlower (mul_pos hC hepsilon).le
    nlinarith only [h1, h2]
  have hqf : q ^ 2 * f ≤ 32 * t := by
    have h := mul_le_mul_of_nonneg_left hfourth (by positivity : 0 ≤ 2 * t)
    exact htlower.trans (by nlinarith only [h])
  have htu : t ≤ (q ^ 2 / s ^ 4) * f := by
    rw [htf]
    exact mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hf.le
  have hqt : q ^ 2 * t ≤ 24 * C * epsilon := by
    calc
      _ ≤ q ^ 2 * ((q ^ 2 / s ^ 4) * f) :=
        mul_le_mul_of_nonneg_left htu (sq_nonneg q)
      _ = (C * epsilon * q ^ 2) * ((q ^ 2 / s ^ 4) * Real.exp (-q / s)) := by
        rw [hfexp]
        ring
      _ ≤ (C * epsilon * q ^ 2) * (24 / q ^ 2) :=
        mul_le_mul_of_nonneg_left (profile_term_le hq0 hs) (by positivity)
      _ = _ := by field_simp [hq0.ne']
  refine ⟨hf, hp, ht, hqp, hpsq, hqf, hqt, ?_⟩
  intro hs1
  have harg : -q ≤ -q / s := (le_div_iff₀ hs).mpr (by nlinarith only [hs1, hq0])
  have hlow : C * epsilon * Real.exp (-q) ≤ f := by
    rw [hfexp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (mul_pos hC hepsilon).le
  have h := (mul_le_mul_of_nonneg_left hlow (sq_nonneg q)).trans hqf
  nlinarith only [h]

theorem exists_smoothProfile_absorption_threshold {K q C : ℝ}
    (hK : 1 ≤ K) (hq : 8 ≤ q) (hC : 0 < C)
    (hgain : 128 * K * Real.exp q / q ^ 2 < C) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ delta →
      ∀ s : ℝ, 0 < s → s ≤ 2 →
      let f := smoothProfile C q epsilon s
      let p := deriv (smoothProfile C q epsilon) s
      let t := deriv (deriv (smoothProfile C q epsilon)) s
      0 ≤ f ∧ 0 ≤ p ∧ 0 ≤ t ∧
        2 * (K * epsilon) * p + 2 * p ^ 2 ≤ t / 4 ∧
        2 * (K * epsilon) * p + 2 * p ^ 2 < 1 / 8 ∧
        2 * (K * epsilon) * f ≤ t / 4 ∧
        (1 ≤ s → K * epsilon < t / 4) := by
  have hK0 : 0 < K := by linarith only [hK]
  have hq0 : 0 < q := by linarith only [hq]
  let delta := min (q / (128 * K)) (min (1 / (32 * C)) (q ^ 2 / (256 * K)))
  have hd : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, hd, ?_⟩
  intro epsilon hepsilon he s hs hs2
  obtain ⟨hf, hp, ht, hqp, hpsq, hqf, hqt, htransition⟩ :=
    smoothProfile_absorption_derivatives hC hq hepsilon hs hs2
  let f := smoothProfile C q epsilon s
  let p := deriv (smoothProfile C q epsilon) s
  let t := deriv (deriv (smoothProfile C q epsilon)) s
  change 0 ≤ f ∧ 0 ≤ p ∧ 0 ≤ t ∧
    2 * (K * epsilon) * p + 2 * p ^ 2 ≤ t / 4 ∧
    2 * (K * epsilon) * p + 2 * p ^ 2 < 1 / 8 ∧
    2 * (K * epsilon) * f ≤ t / 4 ∧ (1 ≤ s → K * epsilon < t / 4)
  have hKe : K * epsilon ≤ q / 128 := by
    have heq : epsilon ≤ q / (128 * K) :=
      he.trans (min_le_left _ _)
    have h := (le_div_iff₀ (by positivity : 0 < 128 * K)).mp
      heq
    nlinarith only [h]
  have hCe : C * epsilon ≤ 1 / 32 := by
    have heC : epsilon ≤ 1 / (32 * C) :=
      he.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h := (le_div_iff₀ (by positivity : 0 < 32 * C)).mp
      heC
    nlinarith only [h]
  have hKqe : K * epsilon ≤ q ^ 2 / 256 := by
    have heq2 : epsilon ≤ q ^ 2 / (256 * K) :=
      he.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h := (le_div_iff₀ (by positivity : 0 < 256 * K)).mp
      heq2
    nlinarith only [h]
  have hfirst : 2 * (K * epsilon) * p ≤ t / 8 := by
    have h := mul_le_mul_of_nonneg_right hKe hp
    nlinarith only [h, hqp]
  have hsecond : 2 * p ^ 2 ≤ t / 8 := by
    have h := mul_le_mul_of_nonneg_right hCe ht.le
    nlinarith only [h, hpsq]
  have herr : 2 * (K * epsilon) * p + 2 * p ^ 2 ≤ t / 4 := by
    linarith only [hfirst, hsecond]
  have hq2 : 64 ≤ q ^ 2 := by
    nlinarith only [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 8) hq]
  have hsmall : 2 * (K * epsilon) * p + 2 * p ^ 2 < 1 / 8 := by
    have h := mul_le_mul_of_nonneg_right hq2 ht.le
    nlinarith only [herr, h, hqt, hCe]
  have hamp : 2 * (K * epsilon) * f ≤ t / 4 := by
    have h := mul_le_mul_of_nonneg_right hKqe hf.le
    nlinarith only [h, hqf]
  refine ⟨hf.le, hp, ht.le, herr, hsmall, hamp, ?_⟩
  intro hs1
  have hexp : Real.exp q * Real.exp (-q) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hlarge : 128 * K < C * q ^ 2 * Real.exp (-q) := by
    have h := mul_lt_mul_of_pos_right
      ((div_lt_iff₀ (sq_pos_of_pos hq0)).mp hgain) (Real.exp_pos (-q))
    calc
      128 * K = (128 * K * Real.exp q) * Real.exp (-q) := by
        rw [mul_assoc, hexp, mul_one]
      _ < _ := h
  have h := (mul_lt_mul_of_pos_right hlarge hepsilon).trans_le (htransition hs1)
  nlinarith only [h]

section Geometry

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem laplacian_scalar_profile_germ (D : LeviCivitaData g)
    {F s : M → ℝ} {phi : ℝ → ℝ} {x : M}
    (hphi : ContDiff ℝ ∞ phi) (hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) :
    D.laplacian F x = deriv phi (s x) * D.laplacian s x +
      deriv (deriv phi) (s x) * g.inner x (D.gradient s x) (D.gradient s x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hgrad : (∑ i, (mvfderiv (𝓡 3) s x (b i)) ^ 2) =
      g.inner x (D.gradient s x) (D.gradient s x) := by
    simp_rw [← D.inner_gradient s x]
    exact (b.sum_sq_inner_left (D.gradient s x)).trans
      (real_inner_self_eq_norm_sq (D.gradient s x)).symm
  change (∑ i, D.hessian F x (b i) (b i)) =
    deriv phi (s x) * (∑ i, D.hessian s x (b i) (b i)) + _
  calc
    _ = ∑ i, (deriv phi (s x) * D.hessian s x (b i) (b i) +
        deriv (deriv phi) (s x) * (mvfderiv (𝓡 3) s x (b i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hessian_scalar_profile_germ D hphi hs heq]
      ring
    _ = deriv phi (s x) * (∑ i, D.hessian s x (b i) (b i)) +
        deriv (deriv phi) (s x) * (∑ i, (mvfderiv (𝓡 3) s x (b i)) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hgrad]

theorem scalarCurvature_positiveScaling_profile
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
    (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
      (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
    (s : M → ℝ) (phi : ℝ → ℝ) (hphi : ContDiff ℝ ∞ phi) (x : M)
    (hs : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x)
    (heq : F =ᶠ[nhds x] fun y => phi (s y)) :
    D'.scalarCurvature x = Real.exp (2 * phi (s x)) *
      (D.scalarCurvature x +
        4 * deriv (deriv phi) (s x) * g.inner x (D.gradient s x) (D.gradient s x) +
        4 * deriv phi (s x) * D.laplacian s x -
        2 * (deriv phi (s x)) ^ 2 * g.inner x (D.gradient s x) (D.gradient s x)) := by
  rw [scalarCurvature_positiveScaling_exp g D F hF D' x, heq.self_of_nhds,
    laplacian_scalar_profile_germ D hphi hs heq,
    gradient_scalar_profile_germ D (hphi.differentiable (by simp) (s x))
      (hs.mdifferentiableAt (by simp)) heq]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end Geometry

theorem exists_conformalAbsorption (K q : ℝ) (hK : 1 ≤ K) (hq : 8 ≤ q) :
    ∃ C0 : ℝ, 100 * q < C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∃ delta : ℝ, 0 < delta ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
        (F : M → ℝ) (hF : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ F)
        (D' : LeviCivitaData (positiveScaling g (fun y => Real.exp (-2 * F y))
          (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)))
        (s : M → ℝ) (x : M) (epsilon : ℝ),
        0 < epsilon → epsilon ≤ delta → 0 < s x → s x ≤ 2 →
        ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ s x →
        (F =ᶠ[nhds x] fun y => smoothProfile C q epsilon (s y)) →
        (1 / 2 ≤ g.inner x (D.gradient s x) (D.gradient s x) ∧
          g.inner x (D.gradient s x) (D.gradient s x) ≤ 2) →
        (∀ v : TangentSpace (𝓡 3) x, g.inner x v v = 1 →
          |D.hessian s x v v| ≤ K * epsilon) →
        |D.laplacian s x| ≤ K * epsilon → 1 / 2 ≤ D.scalarCurvature x →
        (∀ v w : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x v w →
          -(K * epsilon) ≤ D.sectionalCurvature x v w) →
        (∀ v w : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x v w →
          (mvfderiv (𝓡 3) s x v) ^ 2 + (mvfderiv (𝓡 3) s x w) ^ 2 ≤ 1 / 2 →
          1 / 8 ≤ D.sectionalCurvature x v w) →
        D.scalarCurvature x ≤ D'.scalarCurvature x ∧
        D'.negativeCurvaturePart x ≤ D.negativeCurvaturePart x ∧
        ((∀ v w : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x v w →
            0 < D.sectionalCurvature x v w) →
          ∀ v w : TangentSpace (𝓡 3) x,
            LeviCivitaData.IsOrthonormalPair
              (positiveScaling g (fun y => Real.exp (-2 * F y))
                (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)) x v w →
            0 < D'.sectionalCurvature x v w) ∧
        (1 ≤ s x → ∀ v w : TangentSpace (𝓡 3) x,
          LeviCivitaData.IsOrthonormalPair
            (positiveScaling g (fun y => Real.exp (-2 * F y))
              (contMDiff_exp_neg_two hF) (fun _ => Real.exp_pos _)) x v w →
          0 < D'.sectionalCurvature x v w) := by
  let C0 := max (100 * q) (128 * K * Real.exp q / q ^ 2) + 1
  have hC0 : 100 * q < C0 :=
    (le_max_left (100 * q) (128 * K * Real.exp q / q ^ 2)).trans_lt
      (lt_add_one _)
  refine ⟨C0, hC0, ?_⟩
  intro C hCC
  have hC : 0 < C := by linarith only [hq, hC0, hCC]
  have hgain : 128 * K * Real.exp q / q ^ 2 < C := by
    have h := le_max_right (100 * q) (128 * K * Real.exp q / q ^ 2)
    dsimp only [C0] at hCC
    linarith only [h, hCC]
  obtain ⟨delta, hdelta, hbounds⟩ := exists_smoothProfile_absorption_threshold hK hq hC hgain
  refine ⟨delta, hdelta, ?_⟩
  intro M _ _ _ g D F hF D' s x epsilon hepsilon he hs0 hs2 hs heq hG hH hLap hR hsec hgap
  obtain ⟨hf, hp, ht, herr, hsmall, hamp, htransition⟩ :=
    hbounds epsilon hepsilon he (s x) hs0 hs2
  let phi := smoothProfile C q epsilon
  let f := phi (s x)
  let p := deriv phi (s x)
  let t := deriv (deriv phi) (s x)
  have hphi : ContDiff ℝ ∞ phi := smoothProfile_contDiff C q epsilon
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hX : D.negativeCurvaturePart x ≤ K * epsilon :=
    negativeCurvaturePart_le_of_sectional_lower_bound D x (mul_nonneg hK0 hepsilon.le) hsec
  have hHa (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
      -(K * epsilon) ≤ D.hessian s x v v := (abs_le.mp (hH v hv)).1
  have hgap' (v w : TangentSpace (𝓡 3) x) (hvw : LeviCivitaData.IsOrthonormalPair g x v w)
      (ha : (mvfderiv (𝓡 3) s x v) ^ 2 + (mvfderiv (𝓡 3) s x w) ^ 2 < 1 / 2) :
      1 / 8 ≤ D.sectionalCurvature x v w := hgap v w hvw ha.le
  have hampX : 2 * D.negativeCurvaturePart x * phi (s x) ≤ deriv (deriv phi) (s x) / 4 := by
    have h := mul_le_mul_of_nonneg_right hX hf
    nlinarith only [h, hamp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [scalarCurvature_positiveScaling_profile g D F hF D' s phi hphi x hs heq]
    have htg := mul_le_mul_of_nonneg_left hG.1 ht
    have hpg := mul_le_mul_of_nonneg_left hG.2 (sq_nonneg p)
    have hpl := mul_le_mul_of_nonneg_left (abs_le.mp hLap).1 hp
    have hbracket : D.scalarCurvature x ≤ D.scalarCurvature x +
        4 * t * g.inner x (D.gradient s x) (D.gradient s x) +
        4 * p * D.laplacian s x -
        2 * p ^ 2 * g.inner x (D.gradient s x) (D.gradient s x) := by
      nlinarith only [htg, hpg, hpl, herr, ht]
    have hexp : 1 ≤ Real.exp (2 * f) := Real.one_le_exp_iff.mpr (by linarith only [hf])
    calc
      D.scalarCurvature x ≤ Real.exp (2 * f) * D.scalarCurvature x := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (by linarith only [hR])
      _ ≤ _ := mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
  · exact negativeCurvaturePart_positiveScaling_profile_le_of_split g D F hF D'
      s phi hphi x hs heq (K * epsilon) (1 / 8) hp ht hHa hG.2 herr hgap' hsmall.le hampX
  · intro hpositive v w hvw
    exact sectionalCurvature_positiveScaling_profile_orthonormal_pos_of_split g D F hF D'
      s phi hphi x hs heq (K * epsilon) (1 / 8) hp ht hHa hG.2 herr hgap'
      hsmall hpositive v w hvw
  · intro hs1 v w hvw
    exact sectionalCurvature_positiveScaling_profile_orthonormal_pos_of_gain g D F hF D'
      s phi hphi x hs heq (K * epsilon) (1 / 8) hp ht hHa hG.2 herr hgap'
      hsmall (hX.trans_lt (htransition hs1)) v w hvw

end PoincareConjecture.M36
