import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessBoundedLocal

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

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin 2) ℝ

theorem suPlaneHarmonic_affine (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hh : SUPlaneHarmonic g f) (a : LoopPlane) (s : ℝ) :
    SUPlaneHarmonic g (fun z => f (a + s • z)) := by
  intro p z hz
  have he := hh p (a + s • z) hz
  let U := extChartAt (𝓡 n) p ∘ f
  let Gamma := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
  have h := suRescale_weightedEuler Gamma U (fun _ => 0) (fun _ => le_rfl) a s 1 1 z
  simp only [sub_self, Real.rpow_zero, one_smul, mul_one] at h
  change _ = s ^ 2 • (∑ i : Fin 2, covDerivAlong Gamma U
    (fun y => fderiv ℝ U y (e i)) (e i) (a + s • z)) at h
  rw [show (∑ i : Fin 2, covDerivAlong Gamma U
    (fun y => fderiv ℝ U y (e i)) (e i) (a + s • z)) = 0 from he, smul_zero] at h
  exact h

theorem suBoundedGradient_sphereLimit [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g)
    (equation : ∀ (p : M) (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
      (center : LoopPlane) (radius : ℝ),
      SUWeakAlphaCoordinate g p 1 u V center radius → ContDiffAt ℝ ∞ u center →
      ∑ i : Fin 2, covDerivAlong
        (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)) u
        (fun y => fderiv ℝ u y (e i)) (e i) center = 0)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (htotal : Tendsto (fun j => m60SphereEnergy g (f j)) atTop
      (𝓝 (sInf (m60SphereArea g ''
        {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}))))
    {B : ℝ} (hbound : ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B) :
    Nonempty (SUMaxGradientLimit g f) := by
  obtain ⟨d, obs, hobs, hemb, hread⟩ := suCompactObservation_exists (n := n) (M := M)
  obtain ⟨f0, k, hk, hn0, hlim⟩ := suBoundedGradient_nonNull_subsequence g f hf hn hbound
  obtain ⟨s, hs, hs1, hnorm⟩ := suBoundedGradient_normalization g f hf hbound
  have hlocal (p : UnitTwoSphere) := suBoundedGradient_chart_limit g regular equation
    obs hobs hemb hread (alpha ∘ k) (f ∘ k) (fun j => hf (k j))
    (ha.comp hk.tendsto_atTop) (fun j => har (k j)) (fun j => heq (k j)) f0 hlim
    (htotal.comp hk.tendsto_atTop) hs hs1 p
    (fun j z => (hnorm (k j) p).1 z) (fun j z => (hnorm (k j) p).2 z)
  have hf0 : ContMDiff (𝓡 2) (𝓡 n) ∞ f0 := by
    intro p
    let c := chartAt LoopPlane p
    let v := fun z => f0 (c.symm (s • z))
    have hv : ContMDiff (𝓡 2) (𝓡 n) ∞ v := (hlocal p).1
    have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c p :=
      contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds (mem_chart_source LoopPlane p))
    have hscale : ContMDiffAt (𝓡 2) (𝓡 2) ∞ (fun x : LoopPlane => s⁻¹ • x) (c p) :=
      (contDiff_id.const_smul s⁻¹).contMDiff.contMDiffAt
    apply ((hv _).comp p (hscale.comp p hc)).congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source LoopPlane p)] with y hy
    change f0 y = f0 (c.symm (s • (s⁻¹ • c y)))
    rw [smul_inv_smul₀ hs.ne', c.left_inv hy]
  let p0 := -m60SpherePole
  let v := fun z => f0 ((chartAt LoopPlane p0).symm (s • z))
  have hvh : SUPlaneHarmonic g v := (hlocal p0).2.1
  have hplane : (fun z => v ((0 : LoopPlane) + s⁻¹ • z)) = f0 ∘ m60SphereParameter := by
    funext z
    simp only [v, zero_add, smul_inv_smul₀ hs.ne', m60SphereParameter,
      m60SphereChart_eq_chartAt, Function.comp_apply, p0]
  have hh := suPlaneHarmonic_affine g v hvh 0 s⁻¹
  rw [hplane] at hh
  have hharm : M60SphereChartHarmonic g f0 := by
    intro p z hz
    simpa only [Fin.sum_univ_two] using hh p z hz
  have hbound0 : m60SphereEnergy g f0 ≤ sInf (m60SphereArea g ''
      {h | ContMDiff (𝓡 2) (𝓡 n) 1 h ∧ ¬ IsNullHomotopicSphere h}) := by
    rw [← (suSphere_rescaled_energy g (hf0.of_le (by simp)) p0 hs).2]
    exact (hlocal p0).2.2.2
  have hnonconstant : ∃ p q : UnitTwoSphere, f0 p ≠ f0 q := by
    by_contra! hc
    apply hn0
    refine ⟨f0.continuous, f0 m60SpherePole, ?_⟩
    have he : f0 = ContinuousMap.const UnitTwoSphere (f0 m60SpherePole) :=
      ContinuousMap.ext fun p => hc p m60SpherePole
    change ContinuousMap.Homotopic f0 (ContinuousMap.const UnitTwoSphere (f0 m60SpherePole))
    rw [he]
    exact ContinuousMap.Homotopic.refl _
  exact ⟨⟨d, obs, hobs, hemb, hread, f0, hf0, hnonconstant, hharm, hbound0, Or.inl hn0⟩⟩

end PoincareConjecture.M60
