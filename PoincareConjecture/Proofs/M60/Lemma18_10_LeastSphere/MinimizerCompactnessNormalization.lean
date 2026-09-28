import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerMaxGradient
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessInterface
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaEnergyMinimizers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

private theorem unbounded_subsequence (a : ℕ → ℝ) (ha : ¬ BddAbove (range a)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ j, 1 ≤ a (k j)) ∧ Tendsto (a ∘ k) atTop atTop := by
  have htail (B : ℝ) (N : ℕ) : ∃ j > N, B < a j := by
    obtain ⟨P, hP⟩ := ((Finset.range (N + 1)).finite_toSet.image a).bddAbove
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := not_bddAbove_iff.mp ha (max B P)
    refine ⟨j, ?_, (le_max_left _ _).trans_lt hj⟩
    by_contra hjN
    have hmem : j ∈ (Finset.range (N + 1) : Set ℕ) := by
      simp only [Finset.mem_coe, Finset.mem_range]
      omega
    have h := hP ⟨j, hmem, rfl⟩
    exact (not_lt_of_ge h) ((le_max_right _ _).trans_lt hj)
  choose next hnext hvalue using fun (j N : ℕ) => htail ((j : ℝ) + 1) N
  let k : ℕ → ℕ := fun j => Nat.recOn j (next 0 0) (fun j old => next (j + 1) old)
  have hk : StrictMono k := strictMono_nat_of_lt_succ fun j => hnext (j + 1) (k j)
  have hb (j : ℕ) : (j : ℝ) + 1 ≤ a (k j) := by
    cases j with
    | zero => exact (hvalue 0 0).le
    | succ j => exact (hvalue (j + 1) (k j)).le
  refine ⟨k, hk, fun j => ?_, ?_⟩
  · exact (le_add_of_nonneg_left (Nat.cast_nonneg j)).trans (hb j)
  · apply tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    change (j : ℝ) ≤ a (k j)
    linarith [hb j]

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suSphereWeightedEuler_rescale
    (g : RiemannianMetric n M) {alpha : ℝ} {f : UnitTwoSphere → M}
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (heq : SUSphereWeightedEuler g alpha f)
    (p : UnitTwoSphere) (a : LoopPlane) (s : ℝ) (b : M) (z : LoopPlane)
    (hz : f ((chartAt LoopPlane p).symm (a + s • z)) ∈ (extChartAt (𝓡 n) b).source) :
    let v := fun y => f ((chartAt LoopPlane p).symm (a + s • y))
    let u := extChartAt (𝓡 n) b ∘ v
    let Gamma := CoordinateExponential.christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm)
    let q := fun y => 2 * m60EnergyDensity g v y / suAlphaRoundFactor (a + s • y)
    ∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma u
      (fun y => (s ^ 2 + q y) ^ (alpha - 1) •
        fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) z = 0 := by
  intro v u Gamma q
  let F := f ∘ (chartAt LoopPlane p).symm
  let U := extChartAt (𝓡 n) b ∘ F
  let Q := fun y => 2 * m60EnergyDensity g F y / suAlphaRoundFactor y
  have hQ (y : LoopPlane) : 0 ≤ Q y :=
    div_nonneg (mul_nonneg (by norm_num) (m60EnergyDensity_nonneg g F y))
      (suRoundFactor_smooth_pos.2 y).le
  have hq (y : LoopPlane) : q y = s ^ 2 * Q (a + s • y) := by
    have h := suRescale_energyDensity g F
      ((hf.comp (suSphereChart_smooth p)).mdifferentiable (by simp)) a s y
    change m60EnergyDensity g v y = _ at h
    dsimp only [q, Q]
    rw [h]
    ring
  have hbase := heq p b (a + s • z) hz
  have h := suRescale_weightedEuler Gamma U Q hQ a s 1 alpha z
  simp only [one_pow, mul_one] at h
  change _ = (s ^ 2 * (s ^ 2) ^ (alpha - 1)) •
    (∑ i : Fin 2, ConnectionVariation.covDerivAlong Gamma U
      (fun y => (1 + Q y) ^ (alpha - 1) •
        fderiv ℝ U y (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (EuclideanSpace.basisFun (Fin 2) ℝ i) (a + s • z)) at h
  rw [hbase, smul_zero] at h
  simpa only [hq, U, F, u, v, Function.comp_def] using h

theorem suBoundedGradient_nonNull_subsequence [CompactSpace M] [T2Space M]
    (g : RiemannianMetric n M) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hn : ∀ j, ¬ IsNullHomotopicSphere (f j)) {B : ℝ}
    (hbound : ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B) :
    ∃ (v : C(UnitTwoSphere, M)) (k : ℕ → ℕ), StrictMono k ∧
      ¬ IsNullHomotopicSphere v ∧
      Tendsto (fun j => (⟨f (k j), (hf (k j)).continuous⟩ : C(UnitTwoSphere, M)))
        atTop (𝓝 v) := by
  let C := ∫ _ : UnitTwoSphere, (1 + B) ^ (2 : ℝ) ∂m60RoundSphereMetric.volumeMeasure
  apply m60SphereAlphaEnergy_nonNull_subsequence g (alpha := 2) (C := C) (by norm_num) f hf hn
  intro j
  apply integral_mono (m60SphereAlphaEnergy_integrable g 2 (f j) (hf j)) (integrable_const _)
  intro p
  exact Real.rpow_le_rpow (by have := m60SphereIntrinsicEnergy_nonneg g (f j) p; positivity)
    (by linarith [hbound j p]) (by norm_num)

theorem suUnboundedGradient_normalized_subsequence
    (g : RiemannianMetric n M) (f : ℕ → UnitTwoSphere → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hbound : ¬ ∃ B : ℝ, ∀ j p, 2 * m60SphereIntrinsicEnergy g (f j) p ≤ B) :
    ∃ (k : ℕ → ℕ) (center : ℕ → UnitTwoSphere) (scale : ℕ → ℝ),
      StrictMono k ∧ (∀ j, 0 < scale j ∧ scale j ≤ 1) ∧ Tendsto scale atTop (𝓝 0) ∧
      let v := fun j z => f (k j) ((chartAt LoopPlane (center j)).symm (scale j • z))
      (∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (v j)) ∧
      (∀ j z, 2 * m60EnergyDensity g (v j) z / suAlphaRoundFactor (scale j • z) ∈ Icc 0 1) ∧
      (∀ j, m60EnergyDensity g (v j) 0 = 1 / 2) ∧
      (∀ j z, m60EnergyDensity g (v j) z ≤ 1 / 2) ∧
      (∀ j, Integrable (m60EnergyDensity g (v j)) ∧
        (∫ z, m60EnergyDensity g (v j) z) = m60SphereEnergy g (f (k j))) := by
  choose p hp using fun j => suSphereGradient_exists_max g ((hf j).of_le (by simp))
  let a := fun j => 2 * m60SphereIntrinsicEnergy g (f j) (p j)
  have ha : ¬ BddAbove (range a) := by
    rintro ⟨B, hB⟩
    apply hbound
    exact ⟨B, fun j x => (hp j x).trans (hB (mem_range_self j))⟩
  obtain ⟨k, hk, hka, hkat⟩ := unbounded_subsequence a ha
  let center := fun j => p (k j)
  let scale := fun j => (Real.sqrt (a (k j)))⁻¹
  let v := fun j z => f (k j) ((chartAt LoopPlane (center j)).symm (scale j • z))
  have hpos (j : ℕ) : 0 < a (k j) := (by norm_num : (0 : ℝ) < 1).trans_le (hka j)
  have hs (j : ℕ) : 0 < scale j := inv_pos.mpr (Real.sqrt_pos.mpr (hpos j))
  have hs1 (j : ℕ) : scale j ≤ 1 := by
    apply (inv_le_one₀ (Real.sqrt_pos.mpr (hpos j))).mpr
    simpa using Real.sqrt_le_sqrt (hka j)
  have hst : Tendsto scale atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hkat)
  have hnorm (j : ℕ) := suSphere_maximum_normalization g
    ((hf (k j)).of_le (by simp)) (center j) (hp (k j)) (hpos j)
  refine ⟨k, center, scale, hk, fun j => ⟨hs j, hs1 j⟩, hst, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hf (k j)).comp ((suSphereChart_smooth (center j)).comp
      (contDiff_id.const_smul (scale j)).contMDiff)
  · intro j z
    exact (hnorm j).2.1 z
  · intro j
    exact (hnorm j).2.2.1
  · intro j z
    exact (hnorm j).2.2.2 z
  · intro j
    exact suSphere_rescaled_energy g ((hf (k j)).of_le (by simp)) (center j) (hs j)

end PoincareConjecture.M60
