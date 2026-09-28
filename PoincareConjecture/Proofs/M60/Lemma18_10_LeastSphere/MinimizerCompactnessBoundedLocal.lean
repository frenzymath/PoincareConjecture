import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessUnbounded

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

theorem suBoundedGradient_normalization
    (g : RiemannianMetric n M) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j)) {B : ℝ}
    (hbound : ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ j p,
      let v := fun z => f j ((chartAt LoopPlane p).symm (s • z))
      (∀ z, 2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) ∈ Icc 0 1) ∧
        ∀ z, m60EnergyDensity g v z ≤ 1 / 2 := by
  let A := max B 1
  let s := (Real.sqrt A)⁻¹
  have hA : 1 ≤ A := le_max_right _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hA0)
  have hs1 : s ≤ 1 := (inv_le_one₀ (Real.sqrt_pos.mpr hA0)).mpr (by
    simpa using Real.sqrt_le_sqrt hA)
  have hnorm : s ^ 2 * A = 1 := by
    dsimp only [s]
    rw [inv_pow, Real.sq_sqrt hA0.le, inv_mul_cancel₀ hA0.ne']
  refine ⟨s, hs, hs1, ?_⟩
  intro j p v
  have hq (z : LoopPlane) : 2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) =
      s ^ 2 * (2 * m60SphereIntrinsicEnergy g (f j) ((chartAt LoopPlane p).symm (s • z))) := by
    rw [suSphere_rescaled_density g ((hf j).of_le (by simp)) p s z]
    field_simp [(suRoundFactor_smooth_pos.2 (s • z)).ne']
  have hupper (z : LoopPlane) :
      2 * m60EnergyDensity g v z / suAlphaRoundFactor (s • z) ≤ 1 := by
    rw [hq]
    exact (mul_le_mul_of_nonneg_left ((hbound j _).trans (le_max_left _ _))
      (sq_nonneg s)).trans_eq hnorm
  refine ⟨fun z => ⟨?_, hupper z⟩, fun z => ?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) (m60EnergyDensity_nonneg g v z))
      (suRoundFactor_smooth_pos.2 _).le
  · have hlambda : suAlphaRoundFactor (s • z) ≤ 1 := by
      unfold suAlphaRoundFactor
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg ‖s • z‖]
    have hh := (div_le_iff₀ (suRoundFactor_smooth_pos.2 (s • z))).mp (hupper z)
    nlinarith

theorem suBoundedGradient_chart_limit [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M)
    (regular : SUAlphaOneSmoothness g)
    (equation : ∀ (p : M) (u : LoopPlane → E) (V : Fin 2 → LoopPlane → E)
      (center : LoopPlane) (radius : ℝ),
      SUWeakAlphaCoordinate g p 1 u V center radius → ContDiffAt ℝ ∞ u center →
      ∑ i : Fin 2, covDerivAlong
        (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)) u
        (fun y => fderiv ℝ u y (e i)) (e i) center = 0)
    {d : ℕ} (obs : M → EuclideanSpace ℝ (Fin d))
    (hobs : ContMDiff (𝓡 n) (𝓡 d) ∞ obs) (hemb : IsClosedEmbedding obs)
    (hread : SUChartReadable (n := n) obs)
    (alpha : ℕ → ℝ) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (ha : Tendsto alpha atTop (𝓝 1)) (har : ∀ j, 1 ≤ alpha j ∧ alpha j ≤ 2)
    (heq : ∀ j, SUSphereWeightedEuler g (alpha j) (f j))
    (f0 : C(UnitTwoSphere, M))
    (hlim : Tendsto (fun j => (⟨f j, (hf j).continuous⟩ : C(UnitTwoSphere, M))) atTop (𝓝 f0))
    {I s : ℝ} (htotal : Tendsto (fun j => m60SphereEnergy g (f j)) atTop (𝓝 I))
    (hs : 0 < s) (hs1 : s ≤ 1) (p : UnitTwoSphere)
    (hq : ∀ j z, 2 * m60EnergyDensity g
      (fun y => f j ((chartAt LoopPlane p).symm (s • y))) z / suAlphaRoundFactor (s • z) ∈ Icc 0 1)
    (henergy : ∀ j z, m60EnergyDensity g
      (fun y => f j ((chartAt LoopPlane p).symm (s • y))) z ≤ 1 / 2) :
    let v := fun z => f0 ((chartAt LoopPlane p).symm (s • z))
    ContMDiff (𝓡 2) (𝓡 n) ∞ v ∧ SUPlaneHarmonic g v ∧
      Integrable (m60EnergyDensity g v) ∧ (∫ z, m60EnergyDensity g v z) ≤ I := by
  intro v
  let fj := fun j z => f j ((chartAt LoopPlane p).symm (s • z))
  have hfj (j : ℕ) : ContMDiff (𝓡 2) (𝓡 n) ∞ (fj j) :=
    (hf j).comp ((suSphereChart_smooth p).comp (contDiff_id.const_smul s).contMDiff)
  obtain ⟨v0, k, hv0, hk, hvlim, hvalues, hderiv⟩ :=
    suNormalized_C1_subsequence g obs hobs hemb hread alpha f hf ha har heq
      (fun _ => p) (fun _ => s) (fun _ => ⟨hs, hs1⟩) henergy
  have hsame : (v0 : LoopPlane → M) = v := by
    funext z
    have h1 := (continuous_eval_const z).tendsto v0 |>.comp hvlim
    have hev := (continuous_eval_const ((chartAt LoopPlane p).symm (s • z))).tendsto f0
    have h2 := hev.comp (hlim.comp hk.tendsto_atTop)
    exact tendsto_nhds_unique h1 h2
  have hweak (a : LoopPlane) := suNormalized_limit_weakCoordinate g obs hobs hread
    (alpha ∘ k) (f ∘ k) (fun j => hf (k j)) (ha.comp hk.tendsto_atTop)
    (fun j => har (k j)) (fun j => heq (k j)) (fun _ => p) (fun _ => s)
    (fun _ => ⟨hs, hs1⟩) tendsto_const_nhds v0 hv0 hvlim hvalues hderiv
    (fun j z => henergy (k j) z) (fun j z => hq (k j) z) a
  obtain ⟨hvs, hvh⟩ := suWeakPlaneCoordinates_smooth_harmonic g regular equation obs v0 hweak
  have htot : Tendsto (fun j => ∫ z, m60EnergyDensity g (fj (k j)) z) atTop (𝓝 I) := by
    have ht := htotal.comp hk.tendsto_atTop
    have he (j : ℕ) := (suSphere_rescaled_energy g ((hf (k j)).of_le (by simp)) p hs).2
    simpa only [Function.comp_def, fj, he] using ht
  obtain ⟨hfin, hb⟩ := suObserved_total_energy_le g obs (hobs.of_le (by simp)) hemb hread
    (fun j => fj (k j)) v0 (fun j => (hfj (k j)).of_le (by simp)) hv0
    hvalues hderiv (fun j => (suSphere_rescaled_energy g ((hf (k j)).of_le (by simp)) p hs).1) htot
  rw [hsame] at hvs hvh hfin hb
  exact ⟨hvs, hvh, hfin, hb⟩

end PoincareConjecture.M60
