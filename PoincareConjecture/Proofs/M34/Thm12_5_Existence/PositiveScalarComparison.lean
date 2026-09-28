import PoincareConjecture.Proofs.M34.Thm12_5_Existence.EndExhaustionLaplacian
import PoincareConjecture.Proofs.M34.Standard.ProperBarrierComparison
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Proofs.M10.ScalarBound
import PoincareConjecture.Proofs.M10.LaplacianLinearity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem partialFlow_positive_scalar_comparison (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hTF : T < F.lifetime) (hsmall : (2 * a / 3) * T < 1)
    (hinit : ∀ x : StandardCapSpace, a ≤ g0.connection.scalarCurvature x) :
    ∀ t ∈ Icc 0 T, ∀ x : StandardCapSpace,
      a / (1 - (2 * a / 3) * t) ≤ (F.flow.connection t).scalarCurvature x := by
  let q := fun t : ℝ => a / (1 - (2 * a / 3) * t)
  let R := fun t x => (F.flow.connection t).scalarCurvature x
  have hden (s : ℝ) (hs : s ∈ Icc 0 T) : 0 < 1 - (2 * a / 3) * s := by
    have h := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 2 * a / 3 by positivity)
    linarith
  have hqpos (s : ℝ) (hs : s ∈ Icc 0 T) : 0 < q s := div_pos ha (hden s hs)
  have hqle (s : ℝ) (hs : s ∈ Icc 0 T) : q s ≤ q T := by
    apply div_le_div_of_nonneg_left ha.le (hden T ⟨hT.le, le_rfl⟩)
    have h := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ 2 * a / 3 by positivity)
    linarith
  have hqderiv (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivAt q ((2 / 3 : ℝ) * q s ^ 2) s := by
    have hd := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).const_mul (2 * a / 3))
    convert! (hasDerivAt_const s a).div hd (ne_of_gt (hden s hs)) using 1
    dsimp only [q]
    simp only [Pi.sub_apply, id_eq, mul_one, zero_sub]
    field_simp
    ring
  have hqc : ContinuousOn q (Icc 0 T) :=
    fun s hs => (hqderiv s hs).continuousAt.continuousWithinAt
  have hsub : Icc 0 T ⊆ Ico 0 F.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTF⟩
  obtain ⟨K, hK, hfull⟩ := F.curvature_locally_bounded T hT.le hTF
  let M := 9 * K
  have hM : 0 ≤ M := mul_nonneg (by norm_num) hK
  have hRbound (s : ℝ) (hs : s ∈ Icc 0 T) (x : StandardCapSpace) : |R s x| ≤ M := by
    have h := M10.abs_scalarCurvature_le (F.flow.metric s) (F.flow.connection s) x
    norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (hfull s hs x)) (by norm_num))
  obtain ⟨C, hC, hlap⟩ := partialFlow_exhaustion_laplacian_bound P E0 F hT.le hTF
  let f := fun s x => R s x - q s
  let v := fun s x => (F.flow.connection s).laplacian (R s) x +
    2 * (F.flow.connection s).ricciNormSq x - (2 / 3 : ℝ) * q s ^ 2
  let c := fun s x => (2 / 3 : ℝ) * (R s x + q s)
  have hRcont := (P.scalar_regular 3 StandardCapSpace _ F.flow).continuousOn.mono
    (prod_mono hsub (Subset.refl univ))
  have hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ) :=
    hRcont.sub (hqc.comp continuousOn_fst (fun _ hp => hp.1))
  have hsmooth (s : ℝ) (_hs : s ∈ Icc 0 T) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (f s) :=
    (contMDiff_scalarCurvature (F.flow.connection s)).sub contMDiff_const
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) (x : StandardCapSpace) :
      HasDerivWithinAt (fun u => f u x) (v s x) (Icc 0 T) s :=
    ((P.scalar_evolution 3 StandardCapSpace _ F.flow s (hsub hs) x).mono hsub).sub
      (hqderiv s hs).hasDerivWithinAt
  have hpair : (⟨F.flow.metric 0, F.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
        ⟨g0.metric, g0.connection⟩ :=
    Sigma.mk.inj_iff.mpr ⟨F.initial_metric, F.initial_connection⟩
  have hzero (x : StandardCapSpace) : 0 ≤ f 0 x := by
    have heq := congrArg (fun p : Σ g : RiemannianMetric 3 StandardCapSpace,
      LeviCivitaData g => p.2.scalarCurvature x) hpair
    change 0 ≤ R 0 x - q 0
    have hq0 : q 0 = a := by simp [q]
    rw [hq0]
    exact sub_nonneg.mpr ((hinit x).trans_eq heq.symm)
  have hlow (s : ℝ) (hs : s ∈ Icc 0 T) (x : StandardCapSpace) :
      -(M + q T) ≤ f s x := by
    have hR := (abs_le.mp (hRbound s hs x)).1
    have hq := hqle s hs
    dsimp only [f]
    linarith
  have hc (s : ℝ) (hs : s ∈ Icc 0 T) (x : StandardCapSpace) :
      c s x ≤ (2 / 3 : ℝ) * (M + q T) := by
    have hR := (abs_le.mp (hRbound s hs x)).2
    have hq := hqle s hs
    dsimp only [c]
    linarith
  have hevol (s : ℝ) (_hs : s ∈ Ioc 0 T) (x : StandardCapSpace) :
      (F.flow.connection s).laplacian (f s) x + c s x * f s x ≤ v s x := by
    have hsq := (F.flow.connection s).scalarCurvature_sq_le x
    norm_num only [Nat.cast_ofNat] at hsq
    dsimp only [f, c, v]
    rw [(F.flow.connection s).laplacian_sub
      (contMDiff_scalarCurvature (F.flow.connection s)) contMDiff_const,
      M10.laplacian_const_scalar, sub_zero]
    dsimp only [R] at *
    nlinarith
  have hA : 0 ≤ (2 / 3 : ℝ) * (M + q T) :=
    mul_nonneg (by norm_num) (add_nonneg hM (hqpos T ⟨hT.le, le_rfl⟩).le)
  have hresult := nonnegative_of_proper_barrier F.flow.metric F.flow.connection
    hT hA hC f v c (endExhaustion g0.cylindrical_end) hf hsmooth hd hzero hlow hc hevol
    (endExhaustion_contMDiff _) (one_le_endExhaustion _) (endExhaustion_sublevel_isCompact _)
    (fun s hs x => ((le_abs_self _).trans (hlap s hs x)).trans
      (le_mul_of_one_le_right hC (one_le_endExhaustion _ x)))
  exact fun s hs x => sub_nonneg.mp (hresult s hs x)

end PoincareConjecture.M34
