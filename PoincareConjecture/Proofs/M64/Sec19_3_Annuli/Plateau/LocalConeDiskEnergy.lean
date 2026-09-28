import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeDiskDensity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeCircleEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

open Proofs.M58

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64LocalConeDiskMap_energy_le (g : RiemannianMetric n M)
    (H : ℝ × (M × M) → M) (gamma : ℝ → M)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hperiod : Function.Periodic gamma curvePeriod)
    (h0 : ∀ x, H (0, gamma 0, gamma x) = gamma 0)
    {B P : ℝ}
    (hF : ContMDiff (𝓡 2) (𝓡 n) 1 (m64LocalConeDiskMap H (gamma 0) gamma))
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H
        (s, gamma 0, gamma t))
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t,
      g.tangentNorm (H (s, gamma 0, gamma t))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u => H (u, gamma 0, gamma t)) s 1) =
          (g.edist (gamma 0) (gamma t)).toReal)
    (hlast : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, ∀ v : TangentSpace (𝓡 n) (gamma t),
      g.tangentNorm (H (s, gamma 0, gamma t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
          (s, gamma 0, gamma t) (0, 0, v)) ≤ B * g.tangentNorm (gamma t) v)
    (hprofile : ∀ r ∈ Icc (0 : ℝ) 1, |deriv diskTimeProfile r| ≤ P) :
    (∫ z in loopDiskSet, m60EnergyDensity g (m64LocalConeDiskMap H (gamma 0) gamma) z) ≤
      (P ^ 2 / 2 * curvePeriod ^ 2 + 2 * B ^ 2) *
        ∫ t in Icc (0 : ℝ) curvePeriod,
          (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  let F := m64LocalConeDiskMap H (gamma 0) gamma
  let speed : ℝ → ℝ := fun t => g.tangentNorm (gamma t) (curveVelocity gamma t)
  let E : ℝ := ∫ t in Icc (0 : ℝ) curvePeriod, speed t ^ 2
  let S : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi
  let q : ℝ → ℝ := fun t => P ^ 2 / 2 * curvePeriod * E + 2 * B ^ 2 * speed t ^ 2
  have hspeedcont : Continuous speed := M04.continuous_pathSpeed g hgamma
  have hq : Continuous q := continuous_const.add
    (continuous_const.mul (hspeedcont.pow 2))
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hSK : S ⊆ K := prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
  have hpolar : Continuous (fun p : ℝ × ℝ =>
      p.1 * m60EnergyDensity g F (p.1 • angularPoint p.2)) :=
    continuous_fst.mul ((m60EnergyDensity_continuous g hF).comp
      (continuous_fst.smul (contDiff_angularPoint.continuous.comp continuous_snd)))
  change (∫ z in loopDiskSet, m60EnergyDensity g F z) ≤ _
  rw [integral_loopDisk_polar]
  calc
    _ ≤ ∫ p in S, q p.2 := by
      apply setIntegral_mono_on (hpolar.continuousOn.integrableOn_compact hK |>.mono_set hSK)
        ((hq.comp continuous_snd).continuousOn.integrableOn_compact hK |>.mono_set hSK)
        (measurableSet_Ioc.prod measurableSet_Ioo)
      intro p hp
      have ht : 1 - diskTimeProfile p.1 ∈ Icc (0 : ℝ) 1 := by
        obtain ⟨hl, hu⟩ := diskTimeProfile_mem_Icc p.1
        constructor <;> linarith
      have hb := m64LocalConeDiskMap_polar_energy_le g H (gamma 0) gamma hperiod h0
        hp.1.1 hp.1.2 p.2 (hgamma.mdifferentiable one_ne_zero _)
        (hF.mdifferentiable one_ne_zero _) ((hH _ ht _).mdifferentiableAt one_ne_zero)
        (hspeed _ ht _) (hlast _ ht _) (hprofile _ ⟨hp.1.1.le, hp.1.2⟩)
      exact hb.trans (by
        have hd : P ^ 2 / 2 * (g.edist (gamma 0) (gamma p.2)).toReal ^ 2 ≤
            P ^ 2 / 2 * curvePeriod * E := by
          simpa only [E, speed, mul_assoc] using mul_le_mul_of_nonneg_left
            (m64_periodic_circle_distance_sq_le_energy g hgamma hperiod p.2)
            (show 0 ≤ P ^ 2 / 2 by positivity)
        exact add_le_add hd le_rfl)
    _ = (P ^ 2 / 2 * curvePeriod ^ 2 + 2 * B ^ 2) * E := by
      have hp : (∫ t in Ioo (-Real.pi) Real.pi, speed t ^ 2) = E :=
        m64_circle_energy_polar_interval g hgamma hperiod
      have hc : (∫ t in Ioo (-Real.pi) Real.pi, (P ^ 2 / 2 * curvePeriod * E)) =
          curvePeriod * (P ^ 2 / 2 * curvePeriod * E) := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
        change (Real.pi - -Real.pi) * _ = curvePeriod * _
        congr 1
        unfold curvePeriod
        ring
      change (∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        q p.2 ∂volume.prod volume) = _
      have heq : (fun p : ℝ × ℝ => q p.2) =
          (fun p => (fun _ : ℝ => 1) p.1 * q p.2) := by funext p; rw [one_mul]
      rw [heq, setIntegral_prod_mul (fun _ : ℝ => 1) q]
      have hr : (∫ _ in Ioc (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
      rw [hr, one_mul]
      dsimp only [q]
      have hi1 : IntegrableOn (fun _ : ℝ => P ^ 2 / 2 * curvePeriod * E)
          (Ioo (-Real.pi) Real.pi) :=
        continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self
      have hi2 : IntegrableOn (fun t : ℝ => 2 * B ^ 2 * speed t ^ 2)
          (Ioo (-Real.pi) Real.pi) :=
        (continuous_const.mul (hspeedcont.pow 2)).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
      rw [integral_add hi1 hi2, hc, integral_const_mul, hp]
      ring

variable [T2Space M]

theorem m64_exists_local_cone_disks
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M)) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ gamma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma →
        Function.Periodic gamma curvePeriod →
        (∀ x, g.edist (gamma 0) (gamma x) ≤ ENNReal.ofReal delta) →
        ∃ F : LoopPlane → M, ContMDiff (𝓡 2) (𝓡 n) 1 F ∧
          (∀ x, F (angularPoint x) = gamma x) ∧
          (∀ z : LoopPlane, ‖z‖ ≤ 1 / 2 → F z = gamma 0) ∧
          (∫ z in loopDiskSet, m60EnergyDensity g F z) ≤
            C * ∫ t in Icc (0 : ℝ) curvePeriod,
              (g.tangentNorm (gamma t) (curveVelocity gamma t)) ^ 2 := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  obtain ⟨r, hr, B, _, H, hH, hgeom, _⟩ := m64_exists_local_cone_interpolator g hcompact
  obtain ⟨P, _, hprofile⟩ := exists_diskTimeProfile_derivative_bound
  have hU : IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
    isOpen_lt continuous_edist continuous_const
  refine ⟨r / 2, half_pos hr, P ^ 2 / 2 * curvePeriod ^ 2 + 2 * B ^ 2,
    by positivity, ?_⟩
  intro gamma hgamma hperiod hshort
  have hHat (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H
        (s, gamma 0, gamma t) := by
    apply (hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ?_)).of_le (by simp)
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      (hshort t).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))⟩
  have h0 (t : ℝ) : H (0, gamma 0, gamma t) = gamma 0 :=
    (hgeom _ _ (hshort t)).1
  have h1 (t : ℝ) : H (1, gamma 0, gamma t) = gamma t :=
    (hgeom _ _ (hshort t)).2.1
  have hF := m64LocalConeDiskMap_contMDiff H (gamma 0) gamma hgamma hperiod h0 hHat
  refine ⟨m64LocalConeDiskMap H (gamma 0) gamma, hF,
    m64LocalConeDiskMap_boundary H (gamma 0) gamma hperiod h1,
    fun z hz => m64LocalConeDiskMap_inner H (gamma 0) gamma h0 hz, ?_⟩
  exact m64LocalConeDiskMap_energy_le g H gamma hgamma hperiod h0 hF hHat
    (fun s hs t => (hgeom _ _ (hshort t)).2.2.1 s hs)
    (fun s hs t => (hgeom _ _ (hshort t)).2.2.2 s hs) hprofile

end PoincareConjecture
