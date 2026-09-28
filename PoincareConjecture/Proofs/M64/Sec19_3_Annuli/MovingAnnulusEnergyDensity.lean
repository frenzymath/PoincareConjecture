import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingCurveEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusIntrinsicTension
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem horizontal_family_embedding_contMDiff (s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞
      (fun q : ℝ × ℝ => (q.1, annulusPoint q.2 s)) := by
  apply contMDiff_iff_contDiff.mpr
  apply ContDiff.prodMk contDiff_fst
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [annulusPoint] using! (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))
  · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => s))

private theorem vertical_family_embedding_contMDiff (x : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞
      (fun q : ℝ × ℝ => (q.1, annulusPoint x q.2)) := by
  apply contMDiff_iff_contDiff.mpr
  apply ContDiff.prodMk contDiff_fst
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => x))
  · simpa [annulusPoint] using! (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × ℝ → ℝ))

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}





theorem m64MovingAnnulus_energyDensity_hasDerivAt
    (D : LeviCivitaData g) {v : ℝ × LoopPlane → M}
    {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    {t x s : ℝ} (hp : (t, annulusPoint x s) ∈ O) :
    HasDerivAt (fun r => m60EnergyDensity g (fun p => v (r, p)) (annulusPoint x s))
      (g.inner (v (t, annulusPoint x s))
        (rampHorizontalCovariantDerivative D (fun y => v (t, annulusPoint y s))
          (fun y => curveVelocity (fun r => v (r, annulusPoint y s)) t) x)
        (curveVelocity (fun y => v (t, annulusPoint y s)) x) +
       g.inner (v (t, annulusPoint x s))
        (rampHorizontalCovariantDerivative D (fun r => v (t, annulusPoint x r))
          (fun r => curveVelocity (fun q => v (q, annulusPoint x r)) t) s)
        (curveVelocity (fun r => v (t, annulusPoint x r)) s)) t := by
  let j0 := fun q : ℝ × ℝ => (q.1, annulusPoint q.2 s)
  let j1 := fun q : ℝ × ℝ => (q.1, annulusPoint x q.2)
  have hj0 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j0 :=
    horizontal_family_embedding_contMDiff s
  have hj1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j1 :=
    vertical_family_embedding_contMDiff x
  let c0 := fun r y => v (r, annulusPoint y s)
  let c1 := fun r z => v (r, annulusPoint x z)
  have hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c0 q.1 q.2) (j0 ⁻¹' O) :=
    hv.comp hj0.contMDiffOn (fun _ hq => hq)
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c1 q.1 q.2) (j1 ⁻¹' O) :=
    hv.comp hj1.contMDiffOn (fun _ hq => hq)
  have h0 := m64MovingCurve_half_energy_hasDerivAt D
    (hO.preimage hj0.continuous) hc0 (show (t, x) ∈ j0 ⁻¹' O from hp)
  have h1 := m64MovingCurve_half_energy_hasDerivAt D
    (hO.preimage hj1.continuous) hc1 (show (t, s) ∈ j1 ⁻¹' O from hp)
  apply (h0.add h1).congr_of_eventuallyEq
  have hline : Continuous (fun r : ℝ => (r, annulusPoint x s)) :=
    continuous_id.prodMk continuous_const
  filter_upwards [hline.continuousAt (hO.mem_nhds hp)] with r hr
  have hmd : MDifferentiableAt (𝓡 2) (𝓡 n) (fun p => v (r, p)) (annulusPoint x s) :=
    ((hv.contMDiffAt (hO.mem_nhds hr)).mdifferentiableAt (by simp)).comp (annulusPoint x s)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) r (annulusPoint x s)).differentiableAt.mdifferentiableAt
  dsimp only [c0, c1, Pi.add_apply]
  rw [m64Annulus_horizontal_velocity hmd, m64Annulus_vertical_velocity hmd]
  simp only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram, EuclideanSpace.basisFun_apply]
  ring





theorem m64MovingAnnulus_energyDensity_derivative_eq_divergence
    (D : LeviCivitaData g) {v : ℝ × LoopPlane → M}
    {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    {t x s : ℝ} (hp : (t, annulusPoint x s) ∈ O) :
    deriv (fun r => m60EnergyDensity g (fun p => v (r, p)) (annulusPoint x s)) t =
      deriv (fun y => g.inner (v (t, annulusPoint y s))
        (curveVelocity (fun r => v (r, annulusPoint y s)) t)
        (curveVelocity (fun z => v (t, annulusPoint z s)) y)) x +
      deriv (fun r => g.inner (v (t, annulusPoint x r))
        (curveVelocity (fun q => v (q, annulusPoint x r)) t)
        (curveVelocity (fun z => v (t, annulusPoint x z)) r)) s -
      g.inner (v (t, annulusPoint x s))
        (curveVelocity (fun r => v (r, annulusPoint x s)) t)
        (rampHorizontalCovariantDerivative D (fun y => v (t, annulusPoint y s))
            (fun y => curveVelocity (fun z => v (t, annulusPoint z s)) y) x +
          rampHorizontalCovariantDerivative D (fun r => v (t, annulusPoint x r))
            (fun r => curveVelocity (fun z => v (t, annulusPoint x z)) r) s) := by
  let j0 := fun q : ℝ × ℝ => (q.1, annulusPoint q.2 s)
  let j1 := fun q : ℝ × ℝ => (q.1, annulusPoint x q.2)
  have hj0 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j0 :=
    horizontal_family_embedding_contMDiff s
  have hj1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × LoopPlane) ∞ j1 :=
    vertical_family_embedding_contMDiff x
  let c0 := fun r y => v (r, annulusPoint y s)
  let c1 := fun r z => v (r, annulusPoint x z)
  have hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c0 q.1 q.2) (j0 ⁻¹' O) :=
    hv.comp hj0.contMDiffOn (fun _ hq => hq)
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c1 q.1 q.2) (j1 ⁻¹' O) :=
    hv.comp hj1.contMDiffOn (fun _ hq => hq)
  have hO0 := hO.preimage hj0.continuous
  have hO1 := hO.preimage hj1.continuous
  have hp0 : (t, x) ∈ j0 ⁻¹' O := hp
  have hp1 : (t, s) ∈ j1 ⁻¹' O := hp
  have h0 := m64MovingCurve_energy_derivative_eq_divergence D hO0 hc0 hp0
  have h1 := m64MovingCurve_energy_derivative_eq_divergence D hO1 hc1 hp1
  rw [(m64MovingCurve_half_energy_hasDerivAt D hO0 hc0 hp0).deriv] at h0
  rw [(m64MovingCurve_half_energy_hasDerivAt D hO1 hc1 hp1).deriv] at h1
  apply (m64MovingAnnulus_energyDensity_hasDerivAt D hO hv hp).deriv.trans
  calc
    _ = _ := congrArg₂ (fun z w : ℝ => z + w) h0 h1
    _ = _ := by
      simp only [c0, c1, map_add]
      ring

variable [T2Space M] [CompactSpace M] {c0 c1 : ℝ → M}






theorem m64MovingAnnulus_energyDensity_divergence_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂MeasureTheory.volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    {v : ℝ × LoopPlane → M} {O : Set (ℝ × LoopPlane)} (hO : IsOpen O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v O)
    (hbase : ∀ p, v (0, p) = A.map p)
    {x s : ℝ} (hp : (0, annulusPoint x s) ∈ O)
    (hinside : annulusPoint x s ∈ m64AnnulusInterior) :
    deriv (fun r => m60EnergyDensity g (fun p => v (r, p)) (annulusPoint x s)) 0 =
      deriv (fun y => g.inner (v (0, annulusPoint y s))
        (curveVelocity (fun r => v (r, annulusPoint y s)) 0)
        (curveVelocity (fun z => v (0, annulusPoint z s)) y)) x +
      deriv (fun r => g.inner (v (0, annulusPoint x r))
        (curveVelocity (fun q => v (q, annulusPoint x r)) 0)
        (curveVelocity (fun z => v (0, annulusPoint x z)) r)) s := by
  have htension :
      rampHorizontalCovariantDerivative D (fun y => v (0, annulusPoint y s))
          (fun y => curveVelocity (fun z => v (0, annulusPoint z s)) y) x +
        rampHorizontalCovariantDerivative D (fun r => v (0, annulusPoint x r))
          (fun r => curveVelocity (fun z => v (0, annulusPoint x z)) r) s = 0 := by
    have htransport := congrArg (fun f : LoopPlane → M =>
      (rampHorizontalCovariantDerivative D (fun y => f (annulusPoint y s))
          (fun y => curveVelocity (fun z => f (annulusPoint z s)) y) x +
        rampHorizontalCovariantDerivative D (fun r => f (annulusPoint x r))
          (fun r => curveVelocity (fun z => f (annulusPoint x z)) r) s :
            EuclideanSpace ℝ (Fin n))) (funext hbase)
    exact htransport.trans (m64Annulus_intrinsic_tension_eq_zero_of_conformal_minimum
      D A hminimum hconformal hA hinside)
  rw [m64MovingAnnulus_energyDensity_derivative_eq_divergence D hO hv hp,
    htension, map_zero, sub_zero]

end PoincareConjecture
