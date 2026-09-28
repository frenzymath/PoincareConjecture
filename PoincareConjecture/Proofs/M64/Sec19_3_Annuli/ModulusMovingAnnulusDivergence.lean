import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusDivergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusIntrinsicTension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64MovingAnnulus_modulusEnergyDensity_eq_current_divergence
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {v : ℝ × LoopPlane → M} {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    (hbase : ∀ p, v (0, p) = A.map p)
    {x s : ℝ} (hp : (0, annulusPoint x s) ∈ O)
    (hinside : annulusPoint x s ∈ m64AnnulusInterior) :
    deriv (fun t => m64ModulusEnergyDensity g r
        (fun p => v (t, p)) (annulusPoint x s)) 0 =
      r * fderiv ℝ (fun p => m64MovingAnnulusCurrent g v 0 (0, p))
        (annulusPoint x s) (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fun p => m64MovingAnnulusCurrent g v 1 (0, p))
        (annulusPoint x s) (EuclideanSpace.single (1 : Fin 2) 1) := by
  let j0 := fun q : ℝ × ℝ => (q.1, annulusPoint q.2 s)
  let j1 := fun q : ℝ × ℝ => (q.1, annulusPoint x q.2)
  have hj0 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j0 := by
    apply contMDiff_iff_contDiff.mpr
    apply ContDiff.prodMk contDiff_fst
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using! (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => s))
  have hj1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j1 := by
    apply contMDiff_iff_contDiff.mpr
    apply ContDiff.prodMk contDiff_fst
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => x))
    · simpa [annulusPoint] using! (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  let c0 := fun t y => v (t, annulusPoint y s)
  let c1 := fun t z => v (t, annulusPoint x z)
  have hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c0 q.1 q.2) (j0 ⁻¹' O) :=
    hv.comp hj0.contMDiffOn (fun _ hq => hq)
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c1 q.1 q.2) (j1 ⁻¹' O) :=
    hv.comp hj1.contMDiffOn (fun _ hq => hq)
  have h0 := m64MovingCurve_half_energy_hasDerivAt D
    (hO.preimage hj0.continuous) hc0 (show (0, x) ∈ j0 ⁻¹' O from hp)
  have h1 := m64MovingCurve_half_energy_hasDerivAt D
    (hO.preimage hj1.continuous) hc1 (show (0, s) ∈ j1 ⁻¹' O from hp)
  have hdensity := ((h0.const_mul r).add (h1.const_mul r⁻¹)).congr_of_eventuallyEq
    (show (fun t => m64ModulusEnergyDensity g r
        (fun p => v (t, p)) (annulusPoint x s)) =ᶠ[𝓝 0] _ from by
      have hline : Continuous (fun t : ℝ => (t, annulusPoint x s)) :=
        continuous_id.prodMk continuous_const
      filter_upwards [hline.continuousAt (hO.mem_nhds hp)] with t ht
      have hmd : MDifferentiableAt (𝓡 2) (𝓡 n)
          (fun p => v (t, p)) (annulusPoint x s) :=
        ((hv.contMDiffAt (hO.mem_nhds ht)).mdifferentiableAt (by simp)).comp
          (annulusPoint x s)
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) t
            (annulusPoint x s)).differentiableAt.mdifferentiableAt
      dsimp only [c0, c1, Pi.add_apply]
      rw [m64Annulus_horizontal_velocity hmd, m64Annulus_vertical_velocity hmd]
      simp only [m64ModulusEnergyDensity, m60AreaGram, EuclideanSpace.basisFun_apply]
      ring)
  have hdiv0 := m64MovingCurve_energy_derivative_eq_divergence D
    (hO.preimage hj0.continuous) hc0 (show (0, x) ∈ j0 ⁻¹' O from hp)
  have hdiv1 := m64MovingCurve_energy_derivative_eq_divergence D
    (hO.preimage hj1.continuous) hc1 (show (0, s) ∈ j1 ⁻¹' O from hp)
  rw [h0.deriv] at hdiv0
  rw [h1.deriv] at hdiv1
  have htension :
      r • rampHorizontalCovariantDerivative D (fun y => v (0, annulusPoint y s))
          (fun y => curveVelocity (fun z => v (0, annulusPoint z s)) y) x +
        r⁻¹ • rampHorizontalCovariantDerivative D (fun y => v (0, annulusPoint x y))
          (fun y => curveVelocity (fun z => v (0, annulusPoint x z)) y) s = 0 := by
    have htransport := congrArg (fun f : LoopPlane → M =>
      (r • rampHorizontalCovariantDerivative D (fun y => f (annulusPoint y s))
          (fun y => curveVelocity (fun z => f (annulusPoint z s)) y) x +
        r⁻¹ • rampHorizontalCovariantDerivative D (fun y => f (annulusPoint x y))
          (fun y => curveVelocity (fun z => f (annulusPoint x z)) y) s :
            EuclideanSpace ℝ (Fin n))) (funext hbase)
    exact htransport.trans (m64Annulus_intrinsic_tension_eq_zero_of_modulus_minimum
      D A hr hminimum hconformal hA hinside)
  have hpair := congrArg (fun w : TangentSpace (𝓡 n) (v (0, annulusPoint x s)) =>
    g.inner (v (0, annulusPoint x s))
      (curveVelocity (fun t => v (t, annulusPoint x s)) 0) w) htension
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hpair
  have hline0 : Continuous (fun y : ℝ => ((0 : ℝ), annulusPoint y s)) := by
    apply Continuous.prodMk continuous_const
    unfold annulusPoint
    fun_prop
  have hline1 : Continuous (fun y : ℝ => ((0 : ℝ), annulusPoint x y)) := by
    apply Continuous.prodMk continuous_const
    unfold annulusPoint
    fun_prop
  have hcur0 := m64MovingAnnulusCurrent_along_slice_hasDerivAt g hO hv 0
    (hO.preimage hline0) (fun _ hy => hy)
    (fun y _ => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_horizontal_hasDerivAt s y) hp
  have hcur1 := m64MovingAnnulusCurrent_along_slice_hasDerivAt g hO hv 1
    (hO.preimage hline1) (fun _ hy => hy)
    (fun y _ => by simpa only [EuclideanSpace.basisFun_apply] using
      m64AnnulusPoint_vertical_hasDerivAt x y) hp
  dsimp only [c0, c1] at hdiv0 hdiv1 hdensity
  rw [hcur0.deriv] at hdiv0
  rw [hcur1.deriv] at hdiv1
  rw [hdensity.deriv, hdiv0, hdiv1]
  simp only [EuclideanSpace.basisFun_apply] at *
  nlinarith [hpair]

end PoincareConjecture
