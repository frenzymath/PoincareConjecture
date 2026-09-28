import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseInteriorStress
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusStressIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.InteriorStressCutoff













set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)





theorem auxiliaryCircle_free_phase_second_stress_zero_cut
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e) (hei : IsEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hR : ∀ q, R (e q) = planarCircleObservation q.1.2)
    {c0 c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {degree : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
      e R c0 c1 H0 H1 (curvePeriod / circumference) degree)
    (g : RiemannianMetric ((n + 1) + 1) Q.charts.Point)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (hB : Continuous B)
    {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hdiag : ∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
      B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = g.inner q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
        e R c0 c1 H0 H1 (curvePeriod / circumference) degree,
      A.annulus.weightedEnergy B r ≤ C.annulus.weightedEnergy B r)
    (hA : ContinuousOn A.annulus.map S)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta) (hrho : ContDiff ℝ ∞ rho)
    (heta0 : eta 0 = 0) (hetaP : eta curvePeriod = 0)
    (hrhoS : tsupport rho ⊆ Ioo (0 : ℝ) 1) :
    let U := fun p =>
      r * B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
    let V := fun p => r⁻¹ *
      (B (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
        B (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))
    (∫ p in S, deriv eta (p 0) * rho (p 1) * (-(r ^ 2) * V p) +
      eta (p 0) * deriv rho (p 1) * U p) = 0 := by
  let G := m60AreaGram g A.annulus.map
  let U := fun p => r * G p 0 0 - r⁻¹ * G p 1 1
  let V := fun p => 2 * r⁻¹ * G p 0 1
  have hsm := auxiliaryCircle_free_phase_contMDiffOn
    P Q e he hei hread R hR A g B hB hb hdiag hr hminimum hA
  have hG (i j : Fin 2) : ContDiffOn ℝ ∞ (fun p => G p i j) S := by
    intro p hp
    exact (m64AreaGram_entry_contDiffAt
      (hsm.contMDiffAt (isOpen_interior.mem_nhds hp)) i j).contDiffWithinAt
  have hi (i j : Fin 2) : Integrable (fun p => G p i j) mu :=
    A.annulus.gram_integrable_of_contMDiffOn g he B hB hei hb hdiag
      (hsm.of_le (by simp)) i j
  have hUi : Integrable U mu := ((hi 0 0).const_mul r).sub ((hi 1 1).const_mul r⁻¹)
  have hVi : Integrable V mu := (hi 0 1).const_mul (2 * r⁻¹)
  have hUV : ∀ p ∈ S, fderiv ℝ U p e1 = r ^ 2 * fderiv ℝ V p e0 := by
    intro p hp
    have hd := ((hG 0 1).contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt (by simp)
    have hw : fderiv ℝ (fun q => -2 * G q 0 1) p e0 =
        -2 * fderiv ℝ (fun q => G q 0 1) p e0 := by
      rw [fderiv_const_mul hd]
      rfl
    have hv : fderiv ℝ V p e0 = 2 * r⁻¹ * fderiv ℝ (fun q => G q 0 1) p e0 := by
      change fderiv ℝ (fun q => (2 * r⁻¹) * G q 0 1) p e0 = _
      rw [fderiv_const_mul hd]
      rfl
    have h := (auxiliaryCircle_free_phase_stress_cauchyRiemann
      P Q e he hei hread R hR A g B hB hb hdiag hr hminimum hA hp).2
    simp only [EuclideanSpace.basisFun_apply] at h
    change fderiv ℝ U p e1 = -r * fderiv ℝ (fun q => -2 * G q 0 1) p e0 at h
    rw [h, hw, hv]
    field_simp [hr.ne']
  have hcut := m64Annulus_second_stress_zero_cut
    ((contDiffOn_const.mul (hG 0 0)).sub (contDiffOn_const.mul (hG 1 1)) |>.of_le (by simp))
    ((contDiffOn_const.mul (hG 0 1)).of_le (by simp))
    hUi hVi hUV heta hrho heta0 hetaP hrhoS
  have hleft : Integrable (fun p : LoopPlane => eta (p 0) * deriv rho (p 1) * U p) mu :=
    m64Annulus_continuous_mul_integrable hUi
      ((heta.continuous.comp (EuclideanSpace.proj 0).continuous).mul
        ((hrho.continuous_deriv (by simp)).comp (EuclideanSpace.proj 1).continuous))
  have hright : Integrable (fun p : LoopPlane => deriv eta (p 0) * rho (p 1) * V p) mu :=
    m64Annulus_continuous_mul_integrable hVi
      (((heta.continuous_deriv (by simp)).comp (EuclideanSpace.proj 0).continuous).mul
        (hrho.continuous.comp (EuclideanSpace.proj 1).continuous))
  calc
    _ = ∫ p in S, (-(r ^ 2)) * (deriv eta (p 0) * rho (p 1) * V p) +
        eta (p 0) * deriv rho (p 1) * U p := by
      apply integral_congr_ae
      filter_upwards [A.annulus.stress_eq_ae_of_contMDiffOn
        g he B hdiag (hsm.of_le (by simp)) r] with p hp
      rw [hp.1, hp.2]
      dsimp only [U, V, G]
      ring
    _ = 0 := by
      rw [integral_add (hright.const_mul _) hleft, integral_const_mul, hcut]
      ring

end PoincareConjecture.M64
