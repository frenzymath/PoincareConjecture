import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeLowerNormalizedWeakData
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RegularCurveBoundaryC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceAffineClassical

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem lower_boundary_contMDiff_representative
    (A : M64FreeWeakPhaseAnnulus (n := n + 1) e Robs c0 c1 H0 H1 k degree)
    (he : ContMDiff (𝓡 (n + 1)) (𝓡 m) ∞ e) (hei : Topology.IsEmbedding e)
    (hread : M60.SUChartReadable (n := n + 1) e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + degree)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + degree)
    {x0 rho K beta : ℝ} (hrho : 0 < rho)
    (hcurve : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 (fun t => c0 (t + A.label0 x0)))
    (hregular : curveVelocity (n := n + 1) (fun t => c0 (t + A.label0 x0)) 0 ≠ 0)
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ m64AnnulusLowerDomain)
    (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.annulus.column i p‖ ^ 2) ≤ K * r ^ beta)
    (g : RiemannianMetric (n + 1) M)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hsymm : ∀ q v w, B q v w = B q w v) (hpos : ∀ q v, 0 ≤ B q v v)
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hcoercive : ∀ (q : M) (v : E),
      v ∈ range (mfderiv (𝓡 (n + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ Cm * B q v v)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 (n + 1)) q),
      B q (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v) = g.inner q v v)
    {modulus : ℝ} (hmod : 0 < modulus)
    (hconf : ∀ p ∈ S, modulus * m60AreaGram g A.annulus.map p 0 0 =
      modulus⁻¹ * m60AreaGram g A.annulus.map p 1 1 ∧ m60AreaGram g A.annulus.map p 0 1 = 0)
    {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hgrowth : let D := m64SourceScale (Real.sqrt modulus) (Real.sqrt_pos.mpr hmod).ne'
      let f := e ∘ (A.annulus.map ∘ D)
      ∀ p ∈ D ⁻¹' S, ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ f) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C0 * ∑ i : Fin 2, ‖fderiv ℝ f p (EuclideanSpace.single i 1)‖ ^ 2) :
    let Phi := m64SourceAffine (annulusPoint x0 0)
      (Real.sqrt modulus) (Real.sqrt_pos.mpr hmod).ne'
    ∃ r : ℝ, 0 < r ∧ ∃ U : LoopPlane → M,
      ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 U
        (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
      EqOn U (A.annulus.map ∘ Phi) (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
      ∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 →
        U z = c0 (A.label0 (x0 + Real.sqrt modulus * z 0)) := by
  let s := Real.sqrt modulus
  have hs : 0 < s := Real.sqrt_pos.mpr hmod
  let Phi := m64SourceAffine (annulusPoint x0 0) s hs.ne'
  let C := fun t => c0 (t + A.label0 x0)
  let ell := fun z : LoopPlane => A.label0 (x0 + s * z 0) - A.label0 x0
  obtain ⟨tau, htau, H, Lambda, hH, hLambda, U, hinto, -, hV, hw, hUc, hUs, hobs,
    htrace, hholder, hdecay⟩ :=
    A.lower_normalized_weak_data he hA hc0 hc1 hH0 hH1 hrho hs hsub hK hbeta henergy
  have hell : ContinuousAt ell 0 :=
    (((A.labels_continuous hH0 hH1).1.comp
      (continuous_const.add (continuous_const.mul (by fun_prop)))).sub
        continuous_const).continuousAt
  have hell0 : ell 0 = 0 := by simp [ell]
  have hforcing := m64SourceAffine_quadratic_growth (e ∘ A.annulus.map)
    (annulusPoint x0 0) s hs.ne' (by simpa only [Function.comp_assoc] using hgrowth)
  let O : Set LoopPlane := ball 0 (2 * tau) ∩ {z | 0 < z 1}
  have hO : IsOpen O := isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hgrowthU (z : LoopPlane) (hz : z ∈ O) :
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ U) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C0 * ∑ i : Fin 2, ‖fderiv ℝ U z (EuclideanSpace.single i 1)‖ ^ 2 := by
    have heq : U =ᶠ[𝓝 z] e ∘ (A.annulus.map ∘ Phi) := by
      filter_upwards [hO.mem_nhds hz] with p hp
      exact hobs hp
    rw [heq.fderiv.fderiv_eq, heq.fderiv_eq]
    exact hforcing z (hinto hz)
  have hconformal (z : LoopPlane) (hz : z ∈ O) :
      m60AreaGram g (A.annulus.map ∘ Phi) z 0 0 =
          m60AreaGram g (A.annulus.map ∘ Phi) z 1 1 ∧
        m60AreaGram g (A.annulus.map ∘ Phi) z 0 1 = 0 :=
    m64AreaGram_sourceAffine_conformal g (annulusPoint x0 0) hmod
      ((hA.contMDiffAt (isOpen_interior.mem_nhds (hinto hz))).mdifferentiableAt (by simp))
      (hconf _ (hinto hz))
  obtain ⟨r, hr, -, -, F, hF, hFeq, hFtrace, -⟩ :=
    m64RegularCurve_boundary_observed_contDiffOn g e he hei hread C hcurve hregular
      B hB hb hsymm hpos hCm hcoercive hdiag U _ (A.annulus.map ∘ Phi) ell htau
      hUc hV hw hUs hobs hell hell0
      (fun z hz hz0 => by
        have h := htrace z (closedBall_subset_closedBall (by linarith : tau ≤ 2 * tau) hz) hz0
        simpa only [C, ell, sub_add_cancel] using h)
      hconformal hC0 hH (half_pos hbeta) hLambda hgrowthU hholder
      (by simpa only [show 2 * (beta / 2) = beta from by ring] using hdecay)
  refine ⟨r, hr, F, hF, hFeq, ?_⟩
  intro z hz hz0
  simpa only [C, ell, sub_add_cancel] using hFtrace z hz hz0

end PoincareConjecture.M64FreeWeakPhaseAnnulus
