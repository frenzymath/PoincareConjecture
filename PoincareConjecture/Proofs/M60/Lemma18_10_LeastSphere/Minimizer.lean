import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.BranchSet
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.PositiveBranchedArea
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerStationarity
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSequence
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessInterface
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularReplacement
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactness
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerSmoothSequence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M]

theorem m60HarmonicSphere_area_pos (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (hnc : ∃ p q, f p ≠ f q) :
    0 < m60SphereArea g f := by
  have hconf := m60WeaklyConformal_of_chartHarmonic g f hf hharm
  exact m60SphereArea_pos_of_finite_branch_set g f (hf.of_le (by simp))
    (m60SphereBranchSet_finite_of_chartHarmonic g f hf hharm hnc)
    (m60WeaklyConformal_injective_off_branchSet g f hconf)

theorem m60LeastSphere_of_nonNull_energy_bound (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (hnc : ∃ p q, f p ≠ f q)
    (hn : ¬ IsNullHomotopicSphere f)
    (hbound : m60SphereEnergy g f ≤ sInf (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h})) :
    M60LeastSphereAreaConclusion g := by
  have hconf := m60WeaklyConformal_of_chartHarmonic g f hf hharm
  have hae := m60SphereArea_eq_energy_of_weaklyConformal g f (hf.of_le (by simp)) hconf
  have hbelow : BddBelow (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, _, rfl⟩
    exact m60SphereArea_nonneg g h
  have hleast (h : UnitTwoSphere → M) (hh : ContMDiff (𝓡 2) (𝓡 n) 1 h)
      (hhn : ¬ IsNullHomotopicSphere h) : m60SphereEnergy g f ≤ m60SphereArea g h :=
    hbound.trans (csInf_le hbelow ⟨h, ⟨hh, hhn⟩, rfl⟩)
  have hstat : M60EnergyStationary g f := m60EnergyStationary_of_least_energy g f hn
    (fun h hh hhn => (hleast h hh hhn).trans
      (m60SphereAreaProperties_of_contMDiff g h hh).area_le_energy)
  have hbranched := m60BranchedMinimalSphere_of_energyStationary g f hf hnc hstat
  refine ⟨m60SphereArea g f, m60BranchedMinimalSphere_area_pos hbranched,
    ?_, f, hbranched, hn, rfl⟩
  intro h hh hsmall
  by_contra hhn
  exact (not_lt_of_ge (hae.le.trans (hleast h hh hhn))) hsmall

theorem m60MaxGradientLimit_nonNull (g : RiemannianMetric n M)
    (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (harea : Tendsto (fun j => m60SphereArea g (f j)) atTop
      (𝓝 (sInf (m60SphereArea g ''
        {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}))))
    (L : M60.SUMaxGradientLimit g f)
    (replacement : M60.M60SphereAnnularReplacement g) :
    ¬ IsNullHomotopicSphere L.sphere := by
  intro hnull
  rcases L.retained with hnL | ⟨k, center, scale, hk, hscale, _, hvalues, hjets, hdisks⟩
  · exact hnL hnull
  let A := m60SphereArea g L.sphere
  let I := sInf (m60SphereArea g ''
    {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h})
  have hA : 0 < A := m60HarmonicSphere_area_pos g L.sphere L.smooth L.harmonic L.nonconstant
  have hi := m60SphereAreaDensity_integrable g L.sphere (L.smooth.of_le (by simp))
  have hlim : Tendsto (fun N : ℕ => ∫ z in Metric.ball (0 : LoopPlane) N,
      m60SphereAreaDensity g L.sphere z) atTop (𝓝 A) := by
    have ht := tendsto_setIntegral_of_monotone
      (fun N : ℕ => measurableSet_ball (x := (0 : LoopPlane)) (ε := (N : ℝ)))
      (fun i j hij => Metric.ball_subset_ball (Nat.cast_le.mpr hij))
      (hi.integrableOn (s := ⋃ N : ℕ, Metric.ball (0 : LoopPlane) (N : ℝ)))
    simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ, A, m60SphereArea] using ht
  obtain ⟨N, hN, hmass⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hlim.eventually (eventually_gt_nhds (show 3 * A / 4 < A by linarith)))).exists
  have hR : (0 : ℝ) < N := by exact_mod_cast hN
  let D := ∫ z in Metric.ball (0 : LoopPlane) (N : ℝ), m60SphereAreaDensity g L.sphere z
  let T := ∫ z in (Metric.closedBall (0 : LoopPlane) (N : ℝ))ᶜ,
    m60SphereAreaDensity g L.sphere z
  have htail : T < A / 4 := by
    have hm : T ≤ ∫ z in (Metric.ball (0 : LoopPlane) (N : ℝ))ᶜ,
        m60SphereAreaDensity g L.sphere z :=
      setIntegral_mono_set hi.integrableOn
        (Eventually.of_forall (m60AreaDensity_nonneg g (L.sphere ∘ m60SphereParameter)))
        (Eventually.of_forall fun _ hx => fun hb => hx (Metric.ball_subset_closedBall hb))
    have hs := integral_add_compl (μ := volume)
      (measurableSet_ball (x := (0 : LoopPlane)) (ε := (N : ℝ))) hi
    change D + _ = A at hs
    change 3 * A / 4 < D at hmass
    linarith
  have hrep := replacement (fun j => f (k j))
    (fun j => (hf (k j)).of_le (by simp)) center scale hscale L.sphere
    (L.smooth.of_le (by simp)) hnull L.dimension L.observation L.observation_smooth
    L.observation_embedding L.observation_readable hvalues hjets N hR (A / 12)
    (by positivity)
  have ha := (harea.comp hk.tendsto_atTop).eventually
    (eventually_lt_nhds (show I < I + A / 12 by linarith))
  have hd := (hdisks N hR).eventually
    (eventually_gt_nhds (show D - A / 12 < D by linarith))
  obtain ⟨j, ⟨h, hh, hclass, hbound⟩, hja, hjd⟩ := (hrep.and (ha.and hd)).exists
  have hhn : ¬ IsNullHomotopicSphere h := by
    rintro ⟨_, p, hp⟩
    exact hn (k j) ⟨(hf (k j)).continuous, p, hclass.symm.trans hp⟩
  have hbelow : BddBelow (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, _, rfl⟩
    exact m60SphereArea_nonneg g v
  have hI : I ≤ m60SphereArea g h := csInf_le hbelow ⟨h, ⟨hh, hhn⟩, rfl⟩
  change m60SphereArea g h ≤ _ - _ + T + A / 12 at hbound
  change m60SphereArea g (f (k j)) < I + A / 12 at hja
  change D - A / 12 < _ at hjd
  change 3 * A / 4 < D at hmass
  linarith

theorem m60LeastSphere_of_perturbedMinimizers [CompactSpace M] (g : RiemannianMetric n M)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (ha : Tendsto alpha atTop (𝓝 1))
    (harange : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 33 / 32)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (hmin : ∀ j (h : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) ∞ h →
      ¬ IsNullHomotopicSphere h →
      m60SphereAlphaEnergy g (alpha j) (f j) ≤ m60SphereAlphaEnergy g (alpha j) h)
    (heuler : ∀ j, M60.SUSphereWeightedEuler g (alpha j) (f j))
    (compactness : M60.SUMaxGradientCompactnessProducer g) : M60LeastSphereAreaConclusion g := by
  obtain ⟨L⟩ := compactness alpha f ha harange hf hn hmin heuler
  have harea := (m60PerturbedMinimizers_area_energy_tendsto g alpha f ha
    (fun j => (harange j).1) hf hn hmin).2.2
  exact m60LeastSphere_of_nonNull_energy_bound g L.sphere L.smooth L.harmonic
    L.nonconstant (m60MaxGradientLimit_nonNull g f hf hn harea L
      (M60.m60Sphere_annular_replacement g)) L.energy_bound

theorem m60LeastSphere_of_suProducers (g : RiemannianMetric n M)
    (hcompact : IsCompact (univ : Set M)) (x : M)
    (hpi : Nontrivial (HomotopyGroup.Pi 2 M x)) : M60LeastSphereAreaConclusion g := by
  let : CompactSpace M := ⟨hcompact⟩
  obtain ⟨alpha, f, ha, harange, hf, hn, hmin, heuler, _⟩ :=
    M60.suSmoothAlphaMinimizingSequence g x hpi
  exact m60LeastSphere_of_perturbedMinimizers g alpha f ha harange hf hn hmin heuler
    (m60PerturbedMinimizers_maxGradientLimit g
      (M60.suWeakAlphaCoordinate_smooth_alpha_one g))

end PoincareConjecture
