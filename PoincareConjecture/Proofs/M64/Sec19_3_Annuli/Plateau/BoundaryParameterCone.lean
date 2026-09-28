import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeCompetitor
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeParameterChord
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeArcCoordinates
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeChartCapture













noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64BoundaryCone

open Proofs.M58

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ





theorem exists_parameter_halfCone {n m N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (N + 1)))
    (P : EuclideanSpace ℝ (Fin (N + 1)) → M)
    (beta : EuclideanSpace ℝ (Fin (N + 1)) → ℝ) (c : ℝ → M) (phase : ℝ → ℝ)
    {Lip : NNReal} {rho delta eta K k p a b r : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) (hK : 0 ≤ K) (hk : k ≠ 0) (hr : 0 < r)
    (hH : ContDiff ℝ 1 H) (hLip : LipschitzWith Lip H)
    (hHD : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    (hP : ContMDiffOn (𝓡 (N + 1)) (𝓡 n) 1 P (ball 0 (2 * rho)))
    (hbeta : ContDiffOn ℝ 1 beta (ball 0 (2 * rho)))
    (hPobs : ∀ y ∈ closedBall 0 rho, R (e (P y)) = angularPoint (k * beta y))
    (hPD : ∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (hcap : ∀ q : M, dist (e q) (e (c p)) < delta →
      ‖H (e q)‖ < rho / 4 ∧ P (H (e q)) = q)
    (haxis : ∀ t ∈ Ioo (-eta) eta,
      H (e (c (t + p))) = EuclideanSpace.single 0 t ∧
        P (EuclideanSpace.single 0 t) = c (t + p))
    (ha : a - p ∈ Ioo (-eta) eta) (hb : b - p ∈ Ioo (-eta) eta)
    (hphase : Continuous phase)
    (hcurveobs : ∀ t, R (e (c t)) = angularPoint (k * phase t))
    (gamma : ℝ → M) (angular : ℝ → EuclideanSpace ℝ (Fin m)) (L : ℝ → ℝ)
    (hgamma : AbsolutelyContinuousOnInterval (e ∘ gamma) 0 Real.pi)
    (hang : MemLp angular 2 (volume.restrict (Icc (0 : ℝ) Real.pi)))
    (hinc : ∀ s ∈ Icc (0 : ℝ) Real.pi, ∀ t ∈ Icc (0 : ℝ) Real.pi,
      e (gamma t) - e (gamma s) = ∫ theta in s..t, angular theta)
    (hg0 : gamma 0 = c a) (hgpi : gamma Real.pi = c b)
    (hL : ContinuousOn L (Icc (0 : ℝ) Real.pi)) (hL0 : L 0 = phase a)
    (hobs : ∀ theta ∈ Icc (0 : ℝ) Real.pi,
      R (e (gamma theta)) = angularPoint (k * L theta))
    (hfirst : dist (e (c a)) (e (c p)) < delta / 2)
    (hsmall : Real.pi * (∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2) <
      (delta / 2) ^ 2) :
    let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
    let label := fun s => AffineMap.lineMap b a ((s + r) / (2 * r))
    ∃ (f : LoopPlane → M) (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
      (u : LoopPlane → ℝ) (W : Fin 2 → LoopPlane → ℝ),
      MemLp (e ∘ f) 2 (volume.restrict S) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict S)) ∧
      MemLp u 2 (volume.restrict S) ∧ (∀ i, MemLp (W i) 2 (volume.restrict S)) ∧
      (∀ i, ∀ z ∈ S, V i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f z))) ∧
      (∀ z ∈ S, R (e (f z)) = angularPoint (k * u z)) ∧
      (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ (i : Fin 2) (j : Fin m),
        (∫ z in S, V i z j * test z + e (f z) j * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            e (gamma theta) j * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, e (c (label s)) j * test (s • basis 0)) ∧
      (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
        (∫ z in S, W i z * test z + u z * fderiv ℝ test z (basis i)) =
          r * (∫ theta in (0 : ℝ)..Real.pi,
            L theta * test (r • angularPoint theta) * angularPoint theta i) -
          (basis 1) i * ∫ s in (-r)..r, phase (label s) * test (s • basis 0)) ∧
      (∫ z in S, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤
        (K ^ 4 / 2) * (1 + 4 * Real.pi ^ 2) *
          ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2 := by
  let v := H ∘ e ∘ gamma
  let d := fun theta => fderiv ℝ H (e (gamma theta)) (angular theta)
  let label := fun s => AffineMap.lineMap b a ((s + r) / (2 * r))
  obtain ⟨hv, hd, hvinc, henergy⟩ := semicircle_coordinates H hH hLip hHD hgamma hang hinc
  obtain ⟨hvbSmall, hinverse⟩ := semicircle_chart_capture e H P (c p) hdelta hcap
    gamma angular hang (hinc 0 ⟨le_rfl, Real.pi_pos.le⟩)
    (by simpa only [hg0] using hfirst) hsmall
  have hvb : MapsTo v (Icc (0 : ℝ) Real.pi) (closedBall 0 rho) := by
    intro theta htheta
    exact ball_subset_closedBall
      ((ball_subset_ball (by linarith : rho / 4 ≤ rho)) (hvbSmall htheta))
  have h0 : v 0 = EuclideanSpace.single 0 (a - p) := by
    change H (e (gamma 0)) = _
    rw [hg0]
    simpa only [sub_add_cancel] using (haxis (a - p) ha).1
  have hpi : v Real.pi = EuclideanSpace.single 0 (b - p) := by
    change H (e (gamma Real.pi)) = _
    rw [hgpi]
    simpa only [sub_add_cancel] using (haxis (b - p) hb).1
  have hdiam (s : ℝ) (hs : s ∈ Icc (-r) r) :
      P (halfConeDiameter r (v 0) (v Real.pi) s) = c (label s) :=
    halfConeDiameter_reconstruct_parameter hr (fun t ht => (haxis t ht).2) ha hb h0 hpi hs
  have hlabel : Continuous label := by
    simp only [label, AffineMap.lineMap_apply_module]
    fun_prop
  have hright : phase (label r) = L 0 := by
    have hratio : (r + r) / (2 * r) = 1 := by
      rw [← two_mul, div_self (mul_ne_zero (by norm_num) hr.ne')]
    simp only [label, hratio, AffineMap.lineMap_apply_one, hL0]
  obtain ⟨f, V, u, W, hf, hV, hu, hW, ht, ho, hgreen, hphaseGreen, hE⟩ :=
    exists_target_phase_halfCone e he R hr hrho hk hK hP hbeta hPobs hPD
      hv hvb hd hvinc hinverse hL hobs hdiam (hphase.comp hlabel).continuousOn
      hright (fun s _ => hcurveobs (label s))
  refine ⟨f, V, u, W, hf, hV, hu, hW, ht, ho, hgreen, hphaseGreen, hE.trans ?_⟩
  calc
    _ ≤ (K ^ 2 / 2) * (1 + 4 * Real.pi ^ 2) *
        (K ^ 2 * ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = _ := by ring

end PoincareConjecture.M64BoundaryCone
