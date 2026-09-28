import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEulerComposition
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology InnerProductSpace SchwartzMap ContDiff LineDeriv

universe u

namespace PoincareConjecture.M65Euler

open DeTurckDomainRegularityNative

private theorem cutoff_vector {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {S : Set LoopPlane}
    (F : M65LocalWeakMap e S) (θ : 𝓢(LoopPlane, ℝ))
    (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ S) :
    ∃ (U : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane))
      (D : Fin 2 → Lp (EuclideanSpace ℝ (Fin N)) 2 (volume : Measure LoopPlane)),
      (U =ᵐ[volume] fun z => θ z • e (F.value z)) ∧
      (∀ i, D i =ᵐ[volume] fun z => θ z • F.derivative i z +
        fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • e (F.value z)) ∧
      ∀ i j (φ : 𝓢(LoopPlane, ℝ)),
        ⟪(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp (D i),
          φ.toLp 2 volume⟫_ℝ =
          -(∫ z, U z j * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  choose u d hu hd hw using fun j => F.cutoff_global j θ hc hs
  let f (z : LoopPlane) := θ z • e (F.value z)
  let g (i : Fin 2) (z : LoopPlane) := θ z • F.derivative i z +
    fderiv ℝ θ z (EuclideanSpace.basisFun (Fin 2) ℝ i) • e (F.value z)
  have hf : MemLp f 2 volume :=
    MemLp.of_eval_piLp fun j => (Lp.memLp (u j)).ae_eq (hu j)
  have hg (i : Fin 2) : MemLp (g i) 2 volume :=
    MemLp.of_eval_piLp fun j => (Lp.memLp (d j i)).ae_eq (hd j i)
  let U := hf.toLp f
  let D (i : Fin 2) := (hg i).toLp (g i)
  have hproj (i : Fin 2) (j : Fin N) :
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLp (D i) = d j i := by
    apply Lp.ext
    filter_upwards [(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).coeFn_compLp
      (D i), (hg i).coeFn_toLp, hd j i] with z hz hdz hdj
    rw [hz, hdz, hdj]
    rfl
  refine ⟨U, D, hf.coeFn_toLp, fun i => (hg i).coeFn_toLp, ?_⟩
  intro i j φ
  rw [hproj, hw j i φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hu j] with z hz hj
  rw [hz, hj]
  rfl

private theorem integral_test_fderiv_zero (φ : 𝓢(LoopPlane, ℝ)) (v : LoopPlane) :
    (∫ z, fderiv ℝ φ z v) = 0 := by
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : LoopPlane => (1 : ℝ)) (g := φ) (v := v)
    (by simpa +instances only [fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul] using!
      (integrable_zero LoopPlane ℝ volume))
    (by simpa only [one_mul] using (∂_{v} φ).integrable)
    (by simpa only [one_mul] using φ.integrable)
    (fun _ _ => differentiableAt_const 1) (fun _ _ => φ.differentiableAt)
  simpa only [one_mul, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul,
    integral_zero, neg_zero] using hi

set_option maxHeartbeats 1600000 in






theorem weak_chain_ball {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {S : Set LoopPlane}
    (F : M65LocalWeakMap e S) (hS : IsOpen S) (x : LoopPlane) {R : ℝ}
    (hR : 0 ≤ R) (hRS : closedBall x R ⊆ S)
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (hh : ContDiff ℝ 1 h)
    (C : NNReal) (hbound : ∀ y, ‖fderiv ℝ h y‖ ≤ (C : ℝ))
    (φ : 𝓢(LoopPlane, ℝ)) (_hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball x R) (i : Fin 2) :
    (∫ z in ball x R, φ z * fderiv ℝ h (e (F.value z)) (F.derivative i z)) =
      -(∫ z in ball x R,
        fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i) * h (e (F.value z))) := by
  obtain ⟨θ, hcθ, hsθ, hone⟩ := M65Interior.exists_disk_cutoff hS x hR hRS
  obtain ⟨U, D, hU, hD, hweak⟩ := cutoff_vector F θ hcθ hsθ
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  let h0 (y : EuclideanSpace ℝ (Fin N)) := h y - h 0
  have hDh (y : EuclideanSpace ℝ (Fin N)) : fderiv ℝ h0 y = fderiv ℝ h y := by
    exact fderiv_sub_const (h 0)
  obtain ⟨V, W, hV, hW, hw⟩ := weak_chain U (D i) b (hweak i) h0
    (hh.sub contDiff_const) (sub_self _) C (fun y => by rw [hDh]; exact hbound y)
  have hφzero (z : LoopPlane) (hz : z ∉ ball x R) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm => hz (hs hm))
  have hφDzero (z : LoopPlane) (hz : z ∉ ball x R) : fderiv ℝ φ z b = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun hm => hz (hs hm)), zero_apply]
  have hleft : (fun z => W z * φ z) =ᵐ[volume]
      fun z => φ z * fderiv ℝ h (e (F.value z)) (F.derivative i z) := by
    filter_upwards [hW, hU, hD i] with z hwz huz hdz
    by_cases hz : z ∈ ball x R
    · rw [hwz, huz, hdz, (hone z (ball_subset_closedBall hz)).2.1,
        (hone z (ball_subset_closedBall hz)).2.2]
      simp only [one_smul, zero_apply, zero_smul, add_zero, hDh, mul_comm]
    · rw [hφzero z hz, mul_zero, zero_mul]
  have hright : (fun z => V z * fderiv ℝ φ z b) =ᵐ[volume]
      fun z => (h (e (F.value z)) - h 0) * fderiv ℝ φ z b := by
    filter_upwards [hV, hU] with z hvz huz
    by_cases hz : z ∈ ball x R
    · rw [hvz, huz, (hone z (ball_subset_closedBall hz)).2.1, one_smul]
    · rw [hφDzero z hz, mul_zero, mul_zero]
  have hshiftI : Integrable
      (fun z => (h (e (F.value z)) - h 0) * fderiv ℝ φ z b) volume :=
    ((Lp.memLp V).integrable_mul ((∂_{b} φ).memLp 2 volume)).congr hright
  have hconstI : Integrable (fun z => h 0 * fderiv ℝ φ z b) volume :=
    (∂_{b} φ).integrable.const_mul (h 0)
  have hrestore : (∫ z, fderiv ℝ φ z b * h (e (F.value z))) =
      ∫ z, (h (e (F.value z)) - h 0) * fderiv ℝ φ z b := by
    calc
      _ = ∫ z, (h (e (F.value z)) - h 0) * fderiv ℝ φ z b +
          h 0 * fderiv ℝ φ z b := integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = _ := by
        rw [integral_add hshiftI hconstI, integral_const_mul, integral_test_fderiv_zero,
          mul_zero, add_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [hφzero z hz, zero_mul])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [hφDzero z hz, zero_mul])]
  have hwφ := hw φ
  rw [inner_schwartz] at hwφ
  rw [integral_congr_ae hleft, integral_congr_ae hright] at hwφ
  rw [hrestore]
  exact hwφ





def compose_on_ball {M : Type u} {N K : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {S : Set LoopPlane}
    (F : M65LocalWeakMap e S) (hS : IsOpen S) (x : LoopPlane) {R : ℝ}
    (hR : 0 ≤ R) (hRS : closedBall x R ⊆ S)
    (h : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin K))
    (hh : ContDiff ℝ 1 h) (C : NNReal)
    (hbound : ∀ y, ‖fderiv ℝ h y‖ ≤ (C : ℝ)) :
    M65LocalWeakMap (fun y : EuclideanSpace ℝ (Fin K) => y) (ball x R) where
  value z := h (e (F.value z))
  derivative i z := fderiv ℝ h (e (F.value z)) (F.derivative i z)
  value_memLp T hT hTS := by
    let : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.mpr hT.measure_lt_top.ne
    have hLip : LipschitzWith C h := lipschitzWith_of_nnnorm_fderiv_le
      (hh.differentiable one_ne_zero) (fun y => hbound y)
    have hLip0 : LipschitzWith C (fun y => h y - h 0) := by
      intro y z
      simpa only [edist_sub_right] using hLip y z
    have hf := F.value_memLp T hT (hTS.trans (ball_subset_closedBall.trans hRS))
    have hh0 := hLip0.comp_memLp (sub_self _) hf
    exact (hh0.add (memLp_const (h 0))).ae_eq
      (ae_of_all _ fun z => sub_add_cancel (h (e (F.value z))) (h 0))
  derivative_memLp i T hT hTS := by
    have hf := F.value_memLp T hT (hTS.trans (ball_subset_closedBall.trans hRS))
    have hd := F.derivative_memLp i T hT (hTS.trans (ball_subset_closedBall.trans hRS))
    exact hd.clm_apply_of_ae_bound
      ((hh.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hf.1)
      (ae_of_all _ fun z => hbound _)
  weak_derivative φ hc hs i j := by
    let pr : EuclideanSpace ℝ (Fin K) →L[ℝ] ℝ := EuclideanSpace.proj j
    have hp : ContDiff ℝ 1 (fun y => h y j) := pr.contDiff.comp hh
    have hd (y : EuclideanSpace ℝ (Fin N)) :
        fderiv ℝ (fun y => h y j) y = pr.comp (fderiv ℝ h y) :=
      (pr.hasFDerivAt.comp y (hh.differentiable one_ne_zero y).hasFDerivAt).fderiv
    have hb (y : EuclideanSpace ℝ (Fin N)) :
        ‖fderiv ℝ (fun y => h y j) y‖ ≤ ((‖pr‖₊ * C : NNReal) : ℝ) := by
      rw [hd, NNReal.coe_mul]
      exact (pr.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (hbound y) (norm_nonneg _))
    have hw := weak_chain_ball F hS x hR hRS (fun y => h y j) hp (‖pr‖₊ * C) hb
      φ hc hs i
    simpa only [hd, ContinuousLinearMap.comp_apply, pr, EuclideanSpace.proj, PiLp.proj_apply]
      using hw

end PoincareConjecture.M65Euler
