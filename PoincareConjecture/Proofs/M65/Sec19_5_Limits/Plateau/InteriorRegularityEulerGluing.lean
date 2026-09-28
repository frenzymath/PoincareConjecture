import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityWeakGluing
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalCutoff











set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology SchwartzMap LineDeriv Manifold ContDiff

namespace PoincareConjecture.M65Euler

private theorem compact_test_green_zero {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U D : Set LoopPlane}
    (F : M65LocalWeakMap e U) (p : 𝓢(LoopPlane, ℝ))
    (hc : HasCompactSupport p) (hpD : tsupport p ⊆ D) (hDU : D ⊆ U)
    (i : Fin 2) (j : Fin N) :
    (∫ z in D, p z * F.derivative i z j +
      fderiv ℝ p z (EuclideanSpace.basisFun (Fin 2) ℝ i) * e (F.value z) j) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hpU := hpD.trans hDU
  have hD := (F.test_derivative_integrable p hc hpU i j).mono_set hDU
  have hV := (F.test_value_integrable p hc hpU i j).mono_set hDU
  have hzero (S : Set LoopPlane) (hs : tsupport p ⊆ S) (z : LoopPlane) (hz : z ∉ S) :
      p z = 0 ∧ fderiv ℝ p z = 0 := by
    have hn : z ∉ tsupport p := fun hm => hz (hs hm)
    exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩
  have hw := F.weak_derivative p hc hpU i j
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [(hzero U hpU z hz).1]; exact zero_mul _)] at hw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [(hzero U hpU z hz).2]; simp only [zero_apply, zero_mul])] at hw
  rw [integral_add hD hV,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [(hzero D hpD z hz).1]; exact zero_mul _),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [(hzero D hpD z hz).2]; simp only [zero_apply, zero_mul]), hw]
  exact neg_add_cancel _

set_option maxHeartbeats 800000 in






theorem exists_supported_replacement {M : Type*} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U V : Set LoopPlane}
    (F : M65LocalWeakMap e U) (G : M65LocalWeakMap e V)
    (x : LoopPlane) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hDU : closedBall x R ⊆ U) (hDV : closedBall x R ⊆ V)
    (hmatch : ∀ᵐ z ∂volume.restrict (closedBall x R),
      z ∉ closedBall x ρ → e (G.value z) = e (F.value z) ∧
        ∀ i, G.derivative i z = F.derivative i z) :
    ∃ H : M65LocalWeakMap e U,
      (∀ z ∈ closedBall x R, H.value z = G.value z ∧
        ∀ i, H.derivative i z = G.derivative i z) ∧
      ∀ z ∉ closedBall x R, H.value z = F.value z ∧
        ∀ i, H.derivative i z = F.derivative i z := by
  obtain ⟨θ, hc, hs, hθ⟩ := M65Interior.exists_disk_cutoff
    isOpen_ball x hρ (closedBall_subset_ball hρR)
  have hθD : tsupport θ ⊆ closedBall x R := hs.trans ball_subset_closedBall
  have hq := G.value_memLp (closedBall x R) (isCompact_closedBall x R) hDV
  have hd := fun i => G.derivative_memLp i (closedBall x R) (isCompact_closedBall x R) hDV
  apply F.exists_disk_replacement x R hDU G.value G.derivative hq hd
  intro ψ i j
  let b := EuclideanSpace.basisFun (Fin 2) ℝ i
  let p := SchwartzMap.smulLeftCLM ℝ θ ψ
  have hp : (p : LoopPlane → ℝ) = fun z => θ z * ψ z :=
    SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth ψ
  have hpθ : tsupport p ⊆ tsupport θ :=
    (SchwartzMap.tsupport_smulLeftCLM_subset θ ψ).trans inter_subset_right
  have hpc : HasCompactSupport p := hc.of_isClosed_subset isClosed_closure hpθ
  have hpD := hpθ.trans hθD
  have hpderiv (z : LoopPlane) :
      fderiv ℝ p z b = θ z * fderiv ℝ ψ z b + fderiv ℝ θ z b * ψ z := by
    rw [hp, fderiv_fun_mul (θ.differentiableAt) (ψ.differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  let green (T : M65LocalWeakMap e U) (φ : 𝓢(LoopPlane, ℝ)) (z : LoopPlane) :=
    φ z * T.derivative i z j + fderiv ℝ φ z b * e (T.value z) j
  let gF (φ : 𝓢(LoopPlane, ℝ)) (z : LoopPlane) := green F φ z
  let gG (φ : 𝓢(LoopPlane, ℝ)) (z : LoopPlane) :=
    φ z * G.derivative i z j + fderiv ℝ φ z b * e (G.value z) j
  have hintF (φ : 𝓢(LoopPlane, ℝ)) : IntegrableOn (gF φ) (closedBall x R) := by
    exact (((φ.memLp 2 volume).restrict _).integrable_mul
      ((F.derivative_memLp i _ (isCompact_closedBall x R) hDU).eval_piLp j)).add
        ((((∂_{b} φ).memLp 2 volume).restrict _).integrable_mul
          ((F.value_memLp _ (isCompact_closedBall x R) hDU).eval_piLp j))
  have hintG (φ : 𝓢(LoopPlane, ℝ)) : IntegrableOn (gG φ) (closedBall x R) := by
    exact (((φ.memLp 2 volume).restrict _).integrable_mul ((hd i).eval_piLp j)).add
      ((((∂_{b} φ).memLp 2 volume).restrict _).integrable_mul (hq.eval_piLp j))
  have hdiff : (fun z => gG ψ z - gF ψ z) =ᵐ[volume.restrict (closedBall x R)]
      fun z => gG p z - gF p z := by
    filter_upwards [hmatch] with z hz
    dsimp only [gF, gG, green]
    by_cases hm : z ∈ closedBall x ρ
    · have hv := (hθ z hm).2.1
      have hD := (hθ z hm).2.2
      rw [hpderiv, congrFun hp z, hv, hD]
      simp only [one_mul, zero_apply, zero_mul, add_zero]
    · obtain ⟨hv, hD⟩ := hz hm
      rw [hv, hD i]
      simp only [sub_self]
  have hzF : (∫ z in closedBall x R, gF p z) = 0 :=
    compact_test_green_zero F p hpc hpD hDU i j
  have hzG : (∫ z in closedBall x R, gG p z) = 0 :=
    compact_test_green_zero G p hpc hpD hDV i j
  have h := integral_congr_ae hdiff
  rw [integral_sub (hintG ψ) (hintF ψ), integral_sub (hintG p) (hintF p), hzG, hzF] at h
  change (∫ z in closedBall x R, gG ψ z) = ∫ z in closedBall x R, gF ψ z
  linarith





theorem supported_energy_le {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {U V : Set LoopPlane}
    (g : RiemannianMetric 3 M) (F : M65LocalWeakMap e U)
    (hmin : M65LocallyMinimizesEnergy g F) (G : M65LocalWeakMap e V)
    (x : LoopPlane) {ρ R : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ < R)
    (hDU : closedBall x R ⊆ U) (hDV : closedBall x R ⊆ V)
    (hmatch : ∀ᵐ z ∂volume.restrict (closedBall x R),
      z ∉ closedBall x ρ → e (G.value z) = e (F.value z) ∧
        ∀ i, G.derivative i z = F.derivative i z) :
    (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤
      ∫ z in closedBall x R, m65EmbeddedEnergyDensity g e G.value G.derivative z := by
  obtain ⟨H, hin, hout⟩ := exists_supported_replacement F G x hρ hρR hDU hDV hmatch
  have hext : H.value =ᵐ[volume.restrict (closedBall x R)ᶜ] F.value :=
    (ae_restrict_mem measurableSet_closedBall.compl).mono (fun z hz => (hout z hz).1)
  have hm := hmin x R (lt_of_le_of_lt hρ hρR) hDU H
    (ae_restrict_of_ae_restrict_of_subset (sdiff_subset_compl U (closedBall x R)) hext)
  have heq : (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e H.value H.derivative z) =
      ∫ z in closedBall x R, m65EmbeddedEnergyDensity g e G.value G.derivative z := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro z hz
    simp only [m65EmbeddedEnergyDensity, (hin z hz).1, (hin z hz).2]
  rwa [heq] at hm

end PoincareConjecture.M65Euler
