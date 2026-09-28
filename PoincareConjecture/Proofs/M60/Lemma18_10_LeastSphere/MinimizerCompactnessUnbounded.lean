import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitRemoval
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitRegularity
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerBubbleLimitDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

set_option maxHeartbeats 2400000 in

theorem suUnboundedGradient_sphereLimit
    (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g)
    (equation : ∀ (p : M) (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
      (center : LoopPlane) (radius : ℝ),
      SUWeakAlphaCoordinate g p 1 u V center radius → ContDiffAt ℝ ∞ u center →
      ∑ i : Fin 2, covDerivAlong
        (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)) u
        (fun y => fderiv ℝ u y (b i)) (b i) center = 0)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (htotal : Tendsto (fun j => m60SphereEnergy g (f j)) atTop
      (𝓝 (sInf (m60SphereArea g ''
        {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}))))
    (hunbounded : ¬ ∃ B : ℝ, ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B) :
    Nonempty (SUMaxGradientLimit g f) := by
  obtain ⟨d, e, he, hei, hread⟩ := suCompactObservation_exists (n := n) (M := M)
  obtain ⟨k0, center, scale, hk0, hs, hscale, hv, hq, hzero, henergy, hintegral⟩ :=
    suUnboundedGradient_normalized_subsequence g f hf hunbounded
  let v := fun j z => f (k0 j) ((chartAt LoopPlane (center j)).symm (scale j • z))
  obtain ⟨v0, k1, hv0, hk1, hlim, hvalues, hderiv⟩ :=
    suNormalized_C1_subsequence g e he hei hread (alpha ∘ k0) (f ∘ k0)
      (fun j => hf (k0 j)) (ha.comp hk0.tendsto_atTop) (fun j => har (k0 j))
      (fun j => heq (k0 j)) center scale hs henergy
  have hweak (a : LoopPlane) := suNormalized_limit_weakCoordinate g e he hread
    (alpha ∘ k0 ∘ k1) (f ∘ k0 ∘ k1) (fun j => hf (k0 (k1 j)))
    (ha.comp (hk0.comp hk1).tendsto_atTop) (fun j => har (k0 (k1 j)))
    (fun j => heq (k0 (k1 j))) (center ∘ k1) (scale ∘ k1) (fun j => hs (k1 j))
    (hscale.comp hk1.tendsto_atTop) v0 hv0 hlim hvalues hderiv
    (fun j z => henergy (k1 j) z) (fun j z => hq (k1 j) z) a
  obtain ⟨hvs, hvh⟩ := suWeakPlaneCoordinates_smooth_harmonic g regular equation e v0 hweak
  have htotal' : Tendsto (fun j => ∫ z, m60EnergyDensity g (v (k1 j)) z) atTop
      (𝓝 (sInf (m60SphereArea g ''
        {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}))) := by
    simpa only [v, fun j => (hintegral (k1 j)).2, Function.comp_def] using
      htotal.comp (hk0.comp hk1).tendsto_atTop
  obtain ⟨hfinite, hbound⟩ := suObserved_total_energy_le g e (he.of_le (by simp)) hei hread
    (fun j => v (k1 j)) v0 (fun j => (hv (k1 j)).of_le (by simp)) hv0
    hvalues hderiv (fun j => (hintegral (k1 j)).1) htotal'
  have ht0 := (suObserved_density_tendsto g e (he.of_le (by simp)) hei hread
    (fun j => v (k1 j)) v0 (fun j => (hv (k1 j)).of_le (by simp)) hv0 0
    (hvalues.tendstoLocallyUniformlyOn.tendsto_at (mem_univ 0))
    (hderiv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ 0))).2
  have hzero0 : m60EnergyDensity g v0 0 = 1 / 2 := tendsto_nhds_unique ht0 (by
    simpa only [v, fun j => hzero (k1 j)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))))
  have hnonconstant : ∃ x y : LoopPlane, v0 x ≠ v0 y := by
    by_contra! h
    have hc : (v0 : LoopPlane → M) = fun _ => v0 0 := funext fun x => h x 0
    have hz : m60EnergyDensity g v0 0 = 0 := by
      rw [hc]
      simp [m60EnergyDensity, m60AreaGram, mfderiv_const, Matrix.trace]
    linarith
  obtain ⟨sphere, hsmooth, hparameter, hharm, henergySphere⟩ :=
    suFiniteEnergyPlane_smooth_sphere_of_finite_energy g v0 hvs hvh hfinite
  refine ⟨⟨d, e, he, hei, hread, sphere, hsmooth, ?_, hharm, ?_, ?_⟩⟩
  · obtain ⟨x, y, hxy⟩ := hnonconstant
    refine ⟨m60SphereParameter x, m60SphereParameter y, ?_⟩
    rw [show sphere (m60SphereParameter x) = v0 x from congrFun hparameter x,
      show sphere (m60SphereParameter y) = v0 y from congrFun hparameter y]
    exact hxy
  · rw [henergySphere]
    exact hbound
  · right
    refine ⟨k0 ∘ k1, center ∘ k1, scale ∘ k1, hk0.comp hk1,
      (fun j => (hs (k1 j)).1), hscale.comp hk1.tendsto_atTop, ?_, ?_, ?_⟩
    · simpa only [hparameter, Function.comp_def] using hvalues
    · simpa only [hparameter, Function.comp_def] using hderiv
    · intro R _
      have h := (suObserved_disk_integrals_tendsto g e (he.of_le (by simp)) hei hread
        (fun j => v (k1 j)) v0 (fun j => (hv (k1 j)).of_le (by simp)) hv0
        hvalues hderiv (fun j z => henergy (k1 j) z) 0 R).1
      simpa only [m60SphereAreaDensity, hparameter, v, Function.comp_def] using h

end PoincareConjecture.M60
