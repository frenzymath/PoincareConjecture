import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusFirstVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64MovingAnnulusCurrent_periodic
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    (hperiodic : ∀ r x s, v (r, annulusPoint (x + curvePeriod) s) =
      v (r, annulusPoint x s)) (r x s : ℝ)
    (hv : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v
      (r, annulusPoint (x + curvePeriod) s)) (i : Fin 2) :
    m64MovingAnnulusCurrent g v i (r, annulusPoint (x + curvePeriod) s) =
      m64MovingAnnulusCurrent g v i (r, annulusPoint x s) := by
  let T : ℝ × LoopPlane := (0, annulusPoint curvePeriod 0)
  let q : ℝ × LoopPlane := (r, annulusPoint x s)
  have htranslate (p : ℝ × LoopPlane) :
      v (T + p) = v p := by
    have hcoords : annulusPoint (p.2 0) (p.2 1) = p.2 := by
      ext j
      fin_cases j <;> simp [annulusPoint]
    have hshift : T + p = (p.1, annulusPoint (p.2 0 + curvePeriod) (p.2 1)) := by
      ext j
      · simp [T]
      · fin_cases j <;> simp [T, annulusPoint, add_comm]
    rw [hshift, hperiodic, hcoords]
  have hTq : T + q = (r, annulusPoint (x + curvePeriod) s) := by
    ext j
    · simp [T, q]
    · fin_cases j <;> simp [T, q, annulusPoint, add_comm]
  have hshift : HasFDerivAt (fun p : ℝ × LoopPlane => T + p)
      (ContinuousLinearMap.id ℝ (ℝ × LoopPlane)) q := (hasFDerivAt_id q).const_add T
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ × LoopPlane) 𝓘(ℝ, ℝ × LoopPlane)
      (fun p : ℝ × LoopPlane => T + p) q := hshift.differentiableAt.mdifferentiableAt
  have hfun : (v ∘ fun p : ℝ × LoopPlane => T + p) = v := funext htranslate
  have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ × LoopPlane))
    (I' := 𝓘(ℝ, ℝ × LoopPlane)) (I'' := 𝓡 n) q (hTq.symm ▸ hv) hmd
  have hdiff : mfderiv 𝓘(ℝ, ℝ × LoopPlane) 𝓘(ℝ, ℝ × LoopPlane)
      (fun p : ℝ × LoopPlane => T + p) q = ContinuousLinearMap.id ℝ (ℝ × LoopPlane) := by
    rw [mfderiv_eq_fderiv]
    exact hshift.fderiv
  rw [hfun, hdiff] at hd
  have hd' : mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v q =
      mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v (T + q) := by
    simpa only [ContinuousLinearMap.comp_id] using! hd
  rw [← hTq]
  change m64MovingAnnulusCurrent g v i (T + q) = m64MovingAnnulusCurrent g v i q
  simp only [m64MovingAnnulusCurrent, ← hd']
  exact congrArg (fun b : M => g.inner b
    (mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v q (1, 0))
    (mfderiv 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v q
      (0, EuclideanSpace.basisFun (Fin 2) ℝ i))) (htranslate q)

variable [T2Space M] [CompactSpace M] {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_periodic_first_variation_of_conformal_minimum
    (D : LeviCivitaData g) (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    {v : ℝ × LoopPlane → M}
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hperiodic : ∀ r x s, v (r, annulusPoint (x + curvePeriod) s) =
      v (r, annulusPoint x s)) :
    let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
      m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 1) -
        m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 0)
    HasDerivAt (fun r => ∫ p in m64AnnulusDomain,
      m60EnergyDensity g (fun z => v (r, z)) p) flux 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
        m64AnnulusArea g (fun p => v (h, p)) ≤ A.area + h * (flux + eta) := by
  let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
    m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 1) -
      m64MovingAnnulusCurrent g v 1 (0, annulusPoint x 0)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hseam : (∫ s in Icc (0 : ℝ) 1,
      m64MovingAnnulusCurrent g v 0 (0, annulusPoint curvePeriod s) -
        m64MovingAnnulusCurrent g v 0 (0, annulusPoint 0 s)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hp : annulusPoint curvePeriod s ∈ m64AnnulusDomain := by
      change 0 ≤ curvePeriod ∧ curvePeriod ≤ curvePeriod ∧ 0 ≤ s ∧ s ≤ 1
      exact ⟨by unfold curvePeriod; positivity, le_rfl, hs⟩
    have hmd := (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
      (show (0, annulusPoint curvePeriod s) ∈ Ioo (-epsilon) epsilon ×ˢ U from
        ⟨hzero, hdom hp⟩))).mdifferentiableAt (by simp)
    have heq := m64MovingAnnulusCurrent_periodic g hperiodic 0 0 s
      (by simpa only [zero_add] using hmd) 0
    simp only [zero_add] at heq
    exact sub_eq_zero.mpr heq
  have hd := m64AnnulusEnergy_intrinsic_boundary_first_variation D A hminimum
    hconformal hepsilon hU hdom hv hbase
  rw [hseam, zero_add] at hd
  refine ⟨hd, ?_⟩
  have hdensity := (m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation
    g hepsilon hU hdom hv).2
  have heq := hdensity.unique hd
  have hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g (fun z => v (0, z)) p 0 0 =
        m60AreaGram g (fun z => v (0, z)) p 1 1 ∧
      m60AreaGram g (fun z => v (0, z)) p 0 1 = 0 :=
    (funext hbase).symm ▸ hconformal
  have hmajor := m64AnnulusArea_forward_majorant_of_conformal_local_variation
    g hepsilon hU hdom hv hconf
  dsimp only at hmajor
  rw [heq] at hmajor
  simpa only [funext hbase, M64Annulus.area] using hmajor

end PoincareConjecture
