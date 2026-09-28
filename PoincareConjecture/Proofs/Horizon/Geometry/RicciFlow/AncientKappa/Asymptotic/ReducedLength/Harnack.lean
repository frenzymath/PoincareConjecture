import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bilinear
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem curvatureOperatorBound_norm {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) :
    D.CurvatureOperatorBound (D.curvatureTensorNorm x) x := by
  intro A _
  let I := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let R : I → I → I → I → ℝ :=
    fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : (I × I) × (I × I) => A z.1.1 z.1.2 * A z.2.1 z.2.2)
    (fun z : (I × I) × (I × I) => R z.1.1 z.1.2 z.2.1 z.2.2)
  have hCS : (∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l) ^ 2 ≤
      (∑ i, ∑ j, A i j ^ 2) ^ 2 * (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) := by
    simpa only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum,
      ← Finset.sum_mul, ← pow_two] using h
  have hA : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR : 0 ≤ ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  change |∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l| ≤
    Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) * ∑ i, ∑ j, A i j ^ 2
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hR]
  nlinarith [hCS]

variable [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

namespace AncientKappaSolution



theorem harnack_operator_bound (K : AncientKappaSolution n M)
    (t : ℝ) (ht : t ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, (K.flow.connection t).CurvatureOperatorBound C x := by
  obtain ⟨C, hC, hbound⟩ := K.bounded_curvature t ht
  refine ⟨C, hC, fun x A hA => ?_⟩
  exact (curvatureOperatorBound_norm (K.flow.connection t) x A hA).trans
    (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hbound x))
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem ricci_neg_neg {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (v : TangentSpace (𝓡 n) x) :
    D.ricci x (-v) (-v) = D.ricci x v v := by
  unfold LeviCivitaData.ricci
  apply Finset.sum_congr rfl
  intro i _
  change (D.curvatureTensor_bilinear_first_third x _ _) (-v) (-v) =
    (D.curvatureTensor_bilinear_first_third x _ _) v v
  simp only [map_neg, LinearMap.neg_apply, neg_neg]



theorem reducedHarnackDensity_lower (K : AncientKappaSolution n M)
    (H : HarnackAncientTheory.{u}) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ)
    (s : ℝ) (hs : s ∈ Ioo 0 τ) :
    -(K.flow.connection (0 - s)).scalarCurvature (r.path.curve s) / s ≤
      reducedHarnackDensity K.flow 0 r.path.curve r.path_scalar_time_derivative s := by
  obtain ⟨dR, hdR, hineq⟩ := H.ancient_differential n M K.flow K.complete
    K.nonnegative_curvature_operator K.harnack_operator_bound K.nonflat
    (0 - s) (by linarith [hs.1]) (r.path.curve s) (-curveVelocity r.path.curve s)
  have hdR' := hdR.hasDerivAt (Iic_mem_nhds (by linarith [hs.1]))
  have hback : HasDerivAt
      (fun z => (K.flow.connection (0 - z)).scalarCurvature (r.path.curve s))
      (-dR) s := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      hdR'.comp s ((hasDerivAt_id s).const_sub 0)
  have hpath := (r.path_scalar_time_derivative_spec s hs).hasDerivAt
    (Icc_mem_nhds hs.1 hs.2)
  have hderiv : r.path_scalar_time_derivative s = -dR := hpath.unique hback
  simp only [ricci_neg_neg, map_neg] at hineq
  unfold reducedHarnackDensity
  rw [hderiv]
  simp only [neg_neg, neg_div]
  linarith



theorem reducedHarnackIntegral_lower (K : AncientKappaSolution n M)
    (H : HarnackAncientTheory.{u}) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    -backwardLLength K.flow 0 0 τ r.path.curve ≤
      reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ := by
  have hpoint (s : ℝ) (hs : s ∈ Ioo 0 τ) :
      -backwardLIntegrand K.flow 0 r.path.curve s ≤
        s * Real.sqrt s * reducedHarnackDensity K.flow 0 r.path.curve
          r.path_scalar_time_derivative s := by
    have h := mul_le_mul_of_nonneg_left (K.reducedHarnackDensity_lower H r s hs)
      (mul_nonneg hs.1.le (Real.sqrt_nonneg s))
    have hcancel : s * Real.sqrt s *
        (-(K.flow.connection (0 - s)).scalarCurvature (r.path.curve s) / s) =
        -Real.sqrt s * (K.flow.connection (0 - s)).scalarCurvature (r.path.curve s) := by
      field_simp [hs.1.ne']
    rw [hcancel] at h
    have hinner : 0 ≤ (K.flow.metric (0 - s)).inner (r.path.curve s)
        (curveVelocity r.path.curve s) (curveVelocity r.path.curve s) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨(K.flow.metric (0 - s)).toRiemannianMetric⟩
      exact real_inner_self_nonneg (x := curveVelocity (n := n) r.path.curve s)
    unfold backwardLIntegrand
    nlinarith [mul_nonneg (Real.sqrt_nonneg s) hinner]
  simpa only [backwardLLength, reducedHarnackIntegral, Pi.neg_apply,
    intervalIntegral.integral_neg]
    using intervalIntegral.integral_mono_on_of_le_Ioo r.tau_pos.le
      r.path.l_integrable.neg r.harnack_integrable hpoint



theorem reducedHarnackIntegral_div_lower (K : AncientKappaSolution n M)
    (H : HarnackAncientTheory.{u}) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    -2 * reducedLength K.flow 0 p q τ / τ ≤
      reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ /
        (τ * Real.sqrt τ) := by
  have hsqrt : 0 < Real.sqrt τ := Real.sqrt_pos.mpr r.tau_pos
  have hlength := (eq_div_iff (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt).ne').mp
    r.path_realizes_reduced_length
  apply (le_div_iff₀ (mul_pos r.tau_pos hsqrt)).mpr
  calc
    (-2 * reducedLength K.flow 0 p q τ / τ) * (τ * Real.sqrt τ) =
        -backwardLLength K.flow 0 0 τ r.path.curve := by
      rw [← hlength]
      field_simp [r.tau_pos.ne']
    _ ≤ _ := K.reducedHarnackIntegral_lower H r


theorem reducedLength_regular_gradient_bound (K : AncientKappaSolution n M)
    (H : HarnackAncientTheory.{u}) {R τ : ℝ} {p q : M}
    (Q : ReducedLengthDifferentialTheory K.flow 0 R)
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    reducedLengthGradientNormSq K.flow 0 r.representative τ q +
        (K.flow.connection (0 - τ)).scalarCurvature q ≤
      3 * reducedLength K.flow 0 p q τ / τ := by
  have h := K.reducedHarnackIntegral_div_lower H r
  have hformula := (Q.regular_point_formulas p q τ r).2.1
  rw [r.representative_eq (q, τ) r.center_mem] at hformula
  dsimp only at hformula
  simp only [mul_div_assoc] at h ⊢
  linarith



theorem reducedLength_regular_time_lower (K : AncientKappaSolution n M)
    (H : HarnackAncientTheory.{u}) {R τ : ℝ} {p q : M}
    (Q : ReducedLengthDifferentialTheory K.flow 0 R)
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    (K.flow.connection (0 - τ)).scalarCurvature q -
        2 * reducedLength K.flow 0 p q τ / τ ≤
      deriv (fun s => r.representative (q, s)) τ := by
  have h := K.reducedHarnackIntegral_div_lower H r
  have hformula := (Q.regular_point_formulas p q τ r).1
  rw [r.representative_eq (q, τ) r.center_mem] at hformula
  have hhalf : reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ /
      (2 * τ * Real.sqrt τ) =
      (reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ /
        (τ * Real.sqrt τ)) / 2 := by ring
  rw [hhalf] at hformula
  dsimp only at hformula
  simp only [mul_div_assoc] at h ⊢
  linarith

end AncientKappaSolution

namespace AncientAsymptoticSolitonPredecessors


theorem regular_reducedLength_gradient_bound {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    reducedLengthGradientNormSq K.flow 0 r.representative τ q +
        (K.flow.connection (0 - τ)).scalarCurvature q ≤
      3 * reducedLength K.flow 0 p q τ / τ := by
  obtain ⟨Q⟩ := P.reduced_length R (r.tau_pos.trans r.tau_lt)
  exact K.reducedLength_regular_gradient_bound P.harnack Q r


theorem regular_reducedLength_time_lower {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    -2 * reducedLength K.flow 0 p q τ / τ ≤
      deriv (fun s => r.representative (q, s)) τ := by
  obtain ⟨Q⟩ := P.reduced_length R (r.tau_pos.trans r.tau_lt)
  obtain ⟨S⟩ := P.structural
  have hscalar := (S.structural M K).scalar_pos (0 - τ) (by linarith [r.tau_pos]) q
  have h := K.reducedLength_regular_time_lower P.harnack Q r
  simp only [mul_div_assoc] at h ⊢
  linarith


theorem continuous_reducedLength {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (p : M) (τ : ℝ) (hτ : 0 < τ) :
    Continuous (fun q => reducedLength K.flow 0 p q τ) := by
  obtain ⟨V⟩ := P.reduced_volume (τ + 1) (by linarith)
  obtain ⟨D⟩ := V.measure_regularity p
  exact D.continuous.comp_continuous (continuous_id.prodMk continuous_const)
    (fun q => ⟨mem_univ q, hτ, by linarith⟩)



theorem scalar_le_reducedLength {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (p q : M) (τ : ℝ) (hτ : 0 < τ) :
    (K.flow.connection (0 - τ)).scalarCurvature q ≤
      3 * reducedLength K.flow 0 p q τ / τ := by
  obtain ⟨Q⟩ := P.reduced_length (τ + 1) (by linarith)
  obtain ⟨U, _, hU, _, hregular⟩ := Q.regular_locus p τ hτ (by linarith)
  have hclosed : IsClosed {q : M | (K.flow.connection (0 - τ)).scalarCurvature q ≤
      3 * reducedLength K.flow 0 p q τ / τ} :=
    isClosed_le (K.flow.connection (0 - τ)).continuous_scalarCurvature
      ((continuous_const.mul (P.continuous_reducedLength p τ hτ)).div_const τ)
  have hsubset : U ⊆ {q : M | (K.flow.connection (0 - τ)).scalarCurvature q ≤
      3 * reducedLength K.flow 0 p q τ / τ} := by
    intro y hy
    obtain ⟨r⟩ := hregular y hy
    have hbound := K.reducedLength_regular_gradient_bound P.harnack Q r
    have hnorm : 0 ≤ reducedLengthGradientNormSq K.flow 0 r.representative τ y :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    exact (le_add_of_nonneg_left hnorm).trans hbound
  exact hclosed.closure_subset_iff.mpr hsubset (hU q)



theorem reducedLength_pos {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) (p q : M) (τ : ℝ) (hτ : 0 < τ) :
    0 < reducedLength K.flow 0 p q τ := by
  obtain ⟨S⟩ := P.structural
  have hscalar := (S.structural M K).scalar_pos (0 - τ) (by linarith) q
  have hbound := P.scalar_le_reducedLength p q τ hτ
  have hpos : 0 < 3 * reducedLength K.flow 0 p q τ :=
    (div_pos_iff.mp (hscalar.trans_le hbound)).resolve_right
      (fun h => (not_lt_of_ge hτ.le) h.2) |>.1
  linarith



theorem regular_reducedLength_time_abs_bound {K : AncientKappaSolution n M}
    (P : AncientAsymptoticSolitonPredecessors K) {R τ : ℝ} {p q : M}
    (r : ReducedLengthRegularPoint K.flow 0 R p q τ) :
    |deriv (fun s => r.representative (q, s)) τ| ≤
      2 * reducedLength K.flow 0 p q τ / τ := by
  obtain ⟨Q⟩ := P.reduced_length R (r.tau_pos.trans r.tau_lt)
  have ht := (Q.regular_point_formulas p q τ r).1
  have hg := (Q.regular_point_formulas p q τ r).2.1
  rw [r.representative_eq (q, τ) r.center_mem] at ht hg
  dsimp only at ht hg
  have hhalf : reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ /
      (2 * τ * Real.sqrt τ) =
      (reducedHarnackIntegral K.flow 0 r.path.curve r.path_scalar_time_derivative τ /
        (τ * Real.sqrt τ)) / 2 := by ring
  rw [hhalf] at ht
  have hnorm : 0 ≤ reducedLengthGradientNormSq K.flow 0 r.representative τ q :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hscalar := P.scalar_le_reducedLength p q τ r.tau_pos
  have hpos := div_pos (P.reducedLength_pos p q τ r.tau_pos) r.tau_pos
  have hlower := P.regular_reducedLength_time_lower r
  simp only [mul_div_assoc] at hscalar hlower ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end AncientAsymptoticSolitonPredecessors

namespace AncientRescalingSequence



theorem scalar_at_base_le {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) :
    ((S.rescaling k).flow.connection (-1)).scalarCurvature (S.base k) ≤
      3 * (n : ℝ) / 2 := by
  have h := P.scalar_le_reducedLength S.reference (S.base k) (S.scale k) (S.scale_pos k)
  have hmul := (le_div_iff₀ (S.scale_pos k)).mp h
  have hdim : 3 * reducedLength K.flow 0 S.reference (S.base k) (S.scale k) ≤
      3 * (n : ℝ) / 2 := by linarith [S.base_reduced_length_bound k]
  rw [(S.rescaling k).scalar_scale (-1) (by norm_num)]
  rw [show S.scale k * (-1) = 0 - S.scale k by ring]
  simpa only [mul_comm] using hmul.trans hdim



theorem curvature_at_base_past_le {K : AncientKappaSolution n M}
    (S : AncientRescalingSequence K) (P : AncientAsymptoticSolitonPredecessors K)
    (k : ℕ) (t : ℝ) (ht : t ≤ -1) :
    ((S.rescaling k).flow.connection t).curvatureTensorNorm (S.base k) ≤
      3 * (n : ℝ) / 2 := by
  obtain ⟨C⟩ := P.structural
  have hscale := S.scale_pos k
  have hbound := (C.structural M K).past_norm_le_scalar
    (S.scale k * t) (S.scale k * (-1))
    (mul_le_mul_of_nonneg_left ht hscale.le) (by nlinarith) (S.base k)
  calc
    ((S.rescaling k).flow.connection t).curvatureTensorNorm (S.base k) =
        S.scale k * (K.flow.connection (S.scale k * t)).curvatureTensorNorm (S.base k) :=
      (S.rescaling k).curvature_norm_scale t (by linarith) (S.base k)
    _ ≤ S.scale k * (K.flow.connection (S.scale k * (-1))).scalarCurvature (S.base k) :=
      mul_le_mul_of_nonneg_left hbound hscale.le
    _ = ((S.rescaling k).flow.connection (-1)).scalarCurvature (S.base k) :=
      ((S.rescaling k).scalar_scale (-1) (by norm_num) (S.base k)).symm
    _ ≤ _ := S.scalar_at_base_le P k

end AncientRescalingSequence

end PoincareConjecture
