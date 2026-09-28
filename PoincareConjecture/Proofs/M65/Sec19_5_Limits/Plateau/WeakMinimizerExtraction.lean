import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryCompactness
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCompactness
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.HilbertSubsequence
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2ClosedTarget
import Mathlib.MeasureTheory.Measure.SeparableMeasure












set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology InnerProductSpace ENNReal

universe u

namespace PoincareConjecture

private theorem m65DiskCoordinate_eq_linear {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)) (j : Fin N) :
    m65DiskCoordinateL2 u j =
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLpL
        2 (volume.restrict loopDiskSet) u := by
  apply Lp.ext
  exact (m65DiskCoordinateL2_coe u j).trans
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).coeFn_compLpL u).symm

private theorem m65DiskCoordinate_norm_le {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)) (j : Fin N) :
    ‖m65DiskCoordinateL2 u j‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [m65DiskCoordinateL2_coe u j] with z hz
  rw [hz]
  exact PiLp.norm_apply_le (u z) j

private theorem m65DiskCoordinate_norm_sum {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)) :
    (∑ j, ‖m65DiskCoordinateL2 u j‖ ^ 2) = ‖u‖ ^ 2 := by
  have hi (j : Fin N) : Integrable (fun z => (u z j) ^ 2)
      (volume.restrict loopDiskSet) := ((Lp.memLp u).eval_piLp j).integrable_sq
  have heq (j : Fin N) : ‖m65DiskCoordinateL2 u j‖ ^ 2 =
      ∫ z in loopDiskSet, (u z j) ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [m65DiskCoordinateL2_coe u j] with z hz
    simp only [hz, Real.norm_eq_abs, sq_abs]
  simp_rw [heq]
  rw [← integral_finsetSum _ fun j _ => hi j, Lp.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  exact ae_of_all _ fun z => (EuclideanSpace.real_norm_sq_eq (u z)).symm






theorem m65WeakDisks_value_subsequence {M : Type u} {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : ℕ → M65WeakDisk e γ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (he : ∀ p, ‖e p‖ ≤ C) (hd : ∀ n i, ‖(F n).derivative i‖ ≤ D) :
    ∃ (σ : ℕ → ℕ)
      (u0 : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)),
      StrictMono σ ∧ Tendsto (fun n => (F (σ n)).embeddedValue) atTop (𝓝 u0) := by
  let coord (j : Fin N) (n : ℕ) := m65DiskCoordinateL2 (F n).embeddedValue j
  have ht (j : Fin N) : TotallyBounded (range (coord j)) := by
    apply m65WeakTrace_disk_totallyBounded (coord j)
      (fun n i => m65DiskCoordinateL2 ((F n).derivative i) j)
      (fun n => m65CircleBoundaryPullback ((F n).boundary j))
      (fun n => (F n).weak_trace j) hC hD
    · intro n
      filter_upwards [m65DiskCoordinateL2_coe (F n).embeddedValue j,
        (F n).embeddedValue_ae] with z hz hv
      rw [hz, hv]
      exact (PiLp.norm_apply_le (e ((F n).value z)) j).trans (he _)
    · intro n i
      exact (m65DiskCoordinate_norm_le ((F n).derivative i) j).trans (hd n i)
  have hc : IsCompact (pi univ (fun j => closure (range (coord j)))) :=
    isCompact_univ_pi (fun j => isCompact_iff_totallyBounded_isComplete.mpr
      ⟨(ht j).closure, isClosed_closure.isComplete⟩)
  obtain ⟨v, _hv, σ, hσ, hlim⟩ := hc.tendsto_subseq
    (fun n j _ => subset_closure (mem_range_self (f := coord j) n))
  let f : LoopPlane → EuclideanSpace ℝ (Fin N) := fun z => WithLp.toLp 2 (fun j => v j z)
  have hf : MemLp f 2 (volume.restrict loopDiskSet) :=
    MemLp.of_eval_piLp (fun j => Lp.memLp (v j))
  let u0 := hf.toLp f
  have hcoord (j : Fin N) : m65DiskCoordinateL2 u0 j = v j := by
    apply Lp.ext
    filter_upwards [m65DiskCoordinateL2_coe u0 j, hf.coeFn_toLp] with z hz hfz
    rw [hz, hfz]
  have hlimj (j : Fin N) : Tendsto (fun n => coord j (σ n)) atTop (𝓝 (v j)) :=
    (tendsto_pi_nhds.mp hlim) j
  have hsq (j : Fin N) : Tendsto (fun n =>
      ‖m65DiskCoordinateL2 ((F (σ n)).embeddedValue - u0) j‖ ^ 2) atTop (𝓝 0) := by
    have heq (n : ℕ) : m65DiskCoordinateL2 ((F (σ n)).embeddedValue - u0) j =
        coord j (σ n) - v j := by
      calc
        _ = m65DiskCoordinateL2 (F (σ n)).embeddedValue j - m65DiskCoordinateL2 u0 j := by
          simp only [m65DiskCoordinate_eq_linear, map_sub]
        _ = _ := by rw [hcoord j]
    simp_rw [heq]
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hlimj j).sub (tendsto_const_nhds (x := v j))).norm.pow 2
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hsq j)
  simp only [m65DiskCoordinate_norm_sum, Finset.sum_const_zero] at hsum
  refine ⟨σ, u0, hσ, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsum.sqrt







theorem m65NormalizedWeakDisks_subsequence
    {M : Type u} [TopologicalSpace M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (F : ℕ → M65WeakDisk e γ) (compact : IsCompact (univ : Set M))
    (he : Continuous e) (hγ : Continuous γ) (hJordan : Function.Injective (e ∘ γ))
    {a b c : LoopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpin : ∀ n, (F n).Normalized a b c) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ n i, ‖(F n).derivative i‖ ≤ D) :
    ∃ (σ : ℕ → ℕ) (G : M65WeakDisk e γ), StrictMono σ ∧ G.Normalized a b c ∧
      Tendsto (fun n => (F (σ n)).embeddedValue) atTop (𝓝 G.embeddedValue) ∧
      (∀ i v, Tendsto (fun n => ⟪(F (σ n)).derivative i, v⟫_ℝ) atTop
        (𝓝 ⟪G.derivative i, v⟫_ℝ)) ∧
      Tendsto (fun n => (F (σ n)).parameter) atTop (𝓝 G.parameter) := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let : Nonempty M := ⟨γ a⟩
  have heK : IsCompact (range e) := by simpa only [image_univ] using compact.image he
  obtain ⟨C0, hC0⟩ := heK.isBounded.exists_norm_le
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have heC (p : M) : ‖e p‖ ≤ C := (hC0 _ (mem_range_self p)).trans (le_max_left _ _)
  have hbudget (n : ℕ) : ‖(F n).derivative 0‖ ^ 2 +
      ‖(F n).derivative 1‖ ^ 2 ≤ 2 * D ^ 2 := by
    nlinarith [(sq_le_sq₀ (norm_nonneg _) hD).mpr (hd n 0),
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hd n 1)]
  obtain ⟨σ1, β, hσ1, hβ, hweakβ, hpinβ⟩ :=
    m65NormalizedWeakDisks_boundary_subsequence F he hγ hJordan hab hac hbc hpin
      (2 * D ^ 2) hbudget
  obtain ⟨σ2, u0, hσ2, hu⟩ := m65WeakDisks_value_subsequence (fun n => F (σ1 n))
    hC hD heC (fun n i => hd (σ1 n) i)
  let d (n : ℕ) : PiLp 2 (fun _ : Fin 2 =>
      Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)) :=
    WithLp.toLp 2 (fun i => (F (σ1 (σ2 n))).derivative i)
  have hdn (n : ℕ) : ‖d n‖ ≤ 2 * D := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i : Fin 2, ‖(F (σ1 (σ2 n))).derivative i‖ ^ 2) ≤ (2 * D) ^ 2
    rw [Fin.sum_univ_two]
    nlinarith [hbudget (σ1 (σ2 n)), sq_nonneg D]
  obtain ⟨d0, σ3, hσ3, _hd0, hweak⟩ :=
    InnerProductSpace.exists_subsequence_tendsto_inner_of_norm_bound d hdn
  let σ := σ1 ∘ σ2 ∘ σ3
  have hstrong : Tendsto (fun n => (F (σ n)).embeddedValue) atTop (𝓝 u0) :=
    hu.comp hσ3.tendsto_atTop
  have hparameter : Tendsto (fun n => (F (σ n)).parameter) atTop (𝓝 β) :=
    (hβ.comp hσ2.tendsto_atTop).comp hσ3.tendsto_atTop
  have hdweak (i : Fin 2) (v : Lp (EuclideanSpace ℝ (Fin N)) 2
      (volume.restrict loopDiskSet)) :
      Tendsto (fun n => ⟪(F (σ n)).derivative i, v⟫_ℝ) atTop (𝓝 ⟪d0 i, v⟫_ℝ) := by
    have hsingle (w : PiLp 2 (fun _ : Fin 2 =>
        Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))) :
        ⟪w, PiLp.single 2 i v⟫_ℝ = ⟪w i, v⟫_ℝ := by
      simp only [PiLp.inner_apply, PiLp.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
    simpa only [hsingle, d, σ, Function.comp_apply, WithLp.ofLp_toLp]
      using hweak (PiLp.single 2 i v)
  have huK : ∀ᵐ z ∂volume.restrict loopDiskSet, u0 z ∈ range e :=
    Lp.ae_mem_of_tendsto_of_isClosed heK.isClosed hstrong (fun n =>
      (F (σ n)).embeddedValue_ae.mono fun z hz => hz ▸ mem_range_self ((F (σ n)).value z))
  let q := fun z : LoopPlane => Function.invFun e (u0 z)
  have hq : u0 =ᵐ[volume.restrict loopDiskSet] fun z => e (q z) := by
    filter_upwards [huK] with z hz
    exact (Function.invFun_eq hz).symm
  let Γ (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun z => e (γ z) j, (EuclideanSpace.proj j).continuous.comp (he.comp hγ)⟩
  choose b0 hb0 using fun j => m65CircleBoundary_continuous_class ((Γ j).comp β)
  have hbstrong (j : Fin N) :
      Tendsto (fun n => m65CircleBoundaryPullback ((F (σ n)).boundary j)) atTop
        (𝓝 (m65CircleBoundaryPullback (b0 j))) := by
    apply m65AngularTrace_tendsto_of_continuous
      (fun n => (Γ j).comp (F (σ n)).parameter) ((Γ j).comp β)
    · exact fun n => (F (σ n)).boundary_ae j
    · exact hb0 j
    · exact ((Γ j).continuous_postcomp.tendsto β).comp hparameter
  have htrace (j : Fin N) : M65DiskWeakTrace (m65DiskCoordinateL2 u0 j)
      (fun i => m65DiskCoordinateL2 (d0 i) j) (m65CircleBoundaryPullback (b0 j)) := by
    apply m65DiskWeakTrace_of_limit (fun n => (F (σ n)).weak_trace j) _ _ (hbstrong j)
    · simp only [m65DiskCoordinate_eq_linear]
      exact ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLpL
        2 (volume.restrict loopDiskSet)).continuous.tendsto u0 |>.comp hstrong
    · intro i v
      let A := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).compLpL
        2 (volume.restrict loopDiskSet)
      simpa only [ContinuousLinearMap.adjoint_inner_right, m65DiskCoordinate_eq_linear]
        using hdweak i (A.adjoint v)
  let G : M65WeakDisk e γ := {
    value := q
    embeddedValue := u0
    embeddedValue_ae := hq
    derivative := fun i => d0 i
    parameter := β
    weakly_monotone := hweakβ
    boundary := b0
    boundary_ae := hb0
    weak_trace := htrace }
  exact ⟨σ, G, hσ1.comp (hσ2.comp hσ3), hpinβ, hstrong, hdweak, hparameter⟩

end PoincareConjecture
