import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryParameterCone
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryParameterLabels
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseTargetSemicircle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseRealSemicircle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58 M64BoundaryCone

local notation "basis" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem lower_halfDisk_cone_replacement {n m N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {e : M → EuclideanSpace ℝ (Fin m)}
    {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
    {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k D)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.annulus.map (interior m64AnnulusDomain))
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin (N + 1)))
    (P : EuclideanSpace ℝ (Fin (N + 1)) → M)
    (beta : EuclideanSpace ℝ (Fin (N + 1)) → ℝ)
    {Lip : NNReal} {rho delta eta K p x width epsilon R : ℝ}
    (hrho : 0 < rho) (hdelta : 0 < delta) (hK : 0 ≤ K) (hk : k ≠ 0)
    (hH : ContDiff ℝ 1 H) (hLip : LipschitzWith Lip H)
    (hHD : ∀ y, ‖fderiv ℝ H y‖ ≤ K)
    (hP : ContMDiffOn (𝓡 (N + 1)) (𝓡 n) 1 P (ball 0 (2 * rho)))
    (hbeta : ContDiffOn ℝ 1 beta (ball 0 (2 * rho)))
    (hPobs : ∀ y ∈ closedBall 0 rho, Robs (e (P y)) = angularPoint (k * beta y))
    (hPD : ∀ y ∈ closedBall 0 rho, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (hcap : ∀ q : M, dist (e q) (e (c0 p)) < delta →
      ‖H (e q)‖ < rho / 4 ∧ P (H (e q)) = q)
    (haxis : ∀ t ∈ Ioo (-eta) eta,
      H (e (c0 (t + p))) = EuclideanSpace.single 0 t ∧
        P (EuclideanSpace.single 0 t) = c0 (t + p))
    (hcurveobs : ∀ t, Robs (e (c0 t)) = angularPoint (k * H0 t))
    (hwindow : ∀ y ∈ Icc (x - width) (x + width),
      A.label0 y - p ∈ Ioo (-eta) eta ∧
        dist (e (c0 (A.label0 y))) (e (c0 p)) < delta / 2)
    (hwidth : 0 < width) (hx : width < x) (hperiod : x + width < curvePeriod)
    (hheight : width < 1) (hepsilon : 0 < epsilon) (hR : R ≤ width) :
    let old := fun z => e (A.annulus.map (z + annulusPoint x 0))
    let col := fun i z => A.annulus.column i (z + annulusPoint x 0)
    let ph := fun z => A.phase (z + annulusPoint x 0)
    let phCol := fun i z => A.phaseColumn i (z + annulusPoint x 0)
    ∀ᵐ r ∂volume.restrict (Icc epsilon R),
      let angular := fun theta => (-r * Real.sin theta) • col 0 (r • angularPoint theta) +
        (r * Real.cos theta) • col 1 (r • angularPoint theta)
      let S := closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}
      Real.pi * (∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2) < (delta / 2) ^ 2 →
      ∃ (sigma : ℝ → ℝ) (f : LoopPlane → M)
        (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m))
        (u : LoopPlane → ℝ) (W : Fin 2 → LoopPlane → ℝ),
        Continuous sigma ∧ Monotone sigma ∧
        (∀ y, sigma (y + curvePeriod) = sigma y + curvePeriod) ∧
        sigma 0 ∈ Icc (0 : ℝ) curvePeriod ∧
        EqOn sigma A.label0 (Icc 0 curvePeriod \ Icc (x - r) (x + r)) ∧
        MemLp (e ∘ f) 2 (volume.restrict S) ∧
        (∀ i, MemLp (V i) 2 (volume.restrict S)) ∧
        MemLp u 2 (volume.restrict S) ∧ (∀ i, MemLp (W i) 2 (volume.restrict S)) ∧
        (∀ i, ∀ z ∈ S, V i z ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f z))) ∧
        (∀ z ∈ S, Robs (e (f z)) = angularPoint (k * u z)) ∧
        (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ (i : Fin 2) (j : Fin m),
          (∫ z in S, V i z j * test z + e (f z) j * fderiv ℝ test z (basis i)) =
            (∫ z in S, col i z j * test z + old z j * fderiv ℝ test z (basis i)) +
            (basis 1) i *
              ((∫ s in (-r)..r, e (c0 (A.label0 (s + x))) j * test (s • basis 0)) -
                ∫ s in (-r)..r, e (c0 (sigma (s + x))) j * test (s • basis 0))) ∧
        (∀ (test : LoopPlane → ℝ), ContDiff ℝ 1 test → ∀ i : Fin 2,
          (∫ z in S, W i z * test z + u z * fderiv ℝ test z (basis i)) =
            (∫ z in S, phCol i z * test z + ph z * fderiv ℝ test z (basis i)) +
            (basis 1) i *
              ((∫ s in (-r)..r, H0 (A.label0 (s + x)) * test (s • basis 0)) -
                ∫ s in (-r)..r, H0 (sigma (s + x)) * test (s • basis 0))) ∧
        (∫ z in S, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤
          (K ^ 4 / 2) * (1 + 4 * Real.pi ^ 2) *
            ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2 := by
  have htarget := A.lower_halfDisk_target_semicircle he hei hA hc0 hc1 hH0 hH1
    hwidth hx hperiod hheight hepsilon hR
  have hphase := A.lower_halfDisk_real_phase he.continuous hH0 hH1
    hx hperiod hheight hepsilon hR
  filter_upwards [htarget, hphase, ae_restrict_mem measurableSet_Icc] with r ht hp hrI
  dsimp only
  intro hsmall
  have hr : 0 < r := hepsilon.trans_le hrI.1
  have hrW : r ≤ width := hrI.2.trans hR
  obtain ⟨hang, gamma, hgc, hg, hgae, hg0, hgpi, hginc, _, hgreen⟩ := ht
  obtain ⟨_, L, hL, _, hL0, _, _, hphaseGreen, hobs⟩ := hp
  have hwr := hwindow (r + x) (by constructor <;> linarith)
  have hwl := hwindow (-r + x) (by constructor <;> linarith)
  have hLc : ContinuousOn L (Icc (0 : ℝ) Real.pi) := by
    simpa only [uIcc_of_le Real.pi_pos.le] using hL.continuousOn
  obtain ⟨f, V, u, W, hf, hV, hu, hW, htan, hmapobs, hgnew, hpnew, hE⟩ :=
    exists_parameter_halfCone e he Robs H P beta c0 H0 hrho hdelta hK hk hr
      hH hLip hHD hP hbeta hPobs hPD hcap haxis hwr.1 hwl.1 H0.continuous
      hcurveobs gamma _ L hg hang hginc hg0 hgpi hLc hL0 (hobs gamma hgc hgae) hwr.2 hsmall
  obtain ⟨sigma, hsc, hsm, hsp, hsn, hschord, hsoutside⟩ :=
    A.exists_lower_parameter_chord_label hH0 hH1
      (show 0 < x - r by linarith) (show x - r < x + r by linarith)
      (show x + r < curvePeriod by linarith)
  let label := fun s => AffineMap.lineMap (A.label0 (-r + x)) (A.label0 (r + x))
    ((s + r) / (2 * r))
  have hlabel (s : ℝ) (hs : s ∈ Icc (-r) r) : sigma (s + x) = label s := by
    rw [hschord (s + x) (by constructor <;> linarith [hs.1, hs.2])]
    have hleft : x - r = -r + x := by ring
    rw [hleft, add_comm x r]
    change AffineMap.lineMap _ _ _ = AffineMap.lineMap _ _ _
    congr 1
    ring
  refine ⟨sigma, f, V, u, W, hsc, hsm, hsp, hsn, hsoutside,
    hf, hV, hu, hW, htan, hmapobs, ?_, ?_, hE⟩
  · intro test htest i j
    have hdiam : (∫ s in (-r)..r, e (c0 (sigma (s + x))) j * test (s • basis 0)) =
        ∫ s in (-r)..r, e (c0 (label s)) j * test (s • basis 0) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hlabel s (by simpa only [uIcc_of_le (by linarith : -r ≤ r)] using hs)]
    rw [hgnew test htest i j, hgreen test htest i j, hdiam]
    ring
  · intro test htest i
    have hdiam : (∫ s in (-r)..r, H0 (sigma (s + x)) * test (s • basis 0)) =
        ∫ s in (-r)..r, H0 (label s) * test (s • basis 0) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [hlabel s (by simpa only [uIcc_of_le (by linarith : -r ≤ r)] using hs)]
    rw [hpnew test htest i, hphaseGreen test htest i, hdiam]
    ring

end PoincareConjecture.M64FreeWeakPhaseAnnulus
