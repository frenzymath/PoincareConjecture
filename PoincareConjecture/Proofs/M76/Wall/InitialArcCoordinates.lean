import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompatibleChartFormula
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import Mathlib.Topology.Path
import Mathlib.Topology.Order.LeftRightNhds











set_option autoImplicit false

open Set Geometry

namespace Geometry




theorem PolyhedralPLInCharts.exists_initial_chart_vector
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F} {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1))
    (B : OpenPartialHomeomorph X F)
    (hcompat : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (hxB : f 0 ∈ B.source) (hBzero : B (f 0) = 0) :
    ∃ d : F, d ≠ 0 ∧ ∃ δ ∈ Ioo (0 : ℝ) 1,
      MapsTo f (Icc 0 δ) B.source ∧
      ∀ t ∈ Icc 0 δ, B (f t) = t • d := by
  classical
  let p : Path (f 0) (f 1) := Path.ofLine hf.continuousOn rfl rfl
  have hN : p.extend ⁻¹' B.source ∈ nhds (0 : ℝ) :=
    (B.open_source.preimage p.continuous_extend).mem_nhds (by
      change p.extend 0 ∈ B.source
      rw [p.extend_zero]
      exact hxB)
  obtain ⟨c0, hc0, hc0B⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (nhdsWithin_le_nhds hN)
  let c : ℝ := min c0 (1 / 2)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hc0le : c ≤ c0 := min_le_left _ _
  have hcle : c ≤ 1 / 2 := min_le_right _ _
  have hcI : Icc (0 : ℝ) c ⊆ Icc 0 1 :=
    fun _ ht => ⟨ht.1, ht.2.trans (by linarith)⟩
  have hfB : MapsTo f (Icc (0 : ℝ) c) B.source := by
    intro t ht
    have h := hc0B ⟨ht.1, ht.2.trans hc0le⟩
    change p.extend t ∈ B.source at h
    rw [p.extend_apply (hcI ht)] at h
    exact h
  have hI := isFinitePLBallPair_Icc hc
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hfinite : FinitePiecewiseAffineOn (B ∘ f) (Icc (0 : ℝ) c) := by
    rw [← hKs]
    exact hf.finitePiecewiseAffineOn_compatible_chart B hcompat K hK
      (hKs.subset.trans hcI) (fun _ ht => hfB (hKs.subset ht))
  let a : ℝ →ᴬ[ℝ] ℝ := c • ContinuousAffineMap.id ℝ ℝ
  have ha : MapsTo a (Icc (0 : ℝ) 1) (Icc 0 c) := by
    intro t ht
    change c * t ∈ Icc (0 : ℝ) c
    exact ⟨mul_nonneg hc.le ht.1, mul_le_of_le_one_right hc.le ht.2⟩
  obtain ⟨ε, hε, A, hA⟩ := hfinite.exists_initial_affine_segment a ha
  have hA0 : A 0 = 0 := by
    have h := hA ⟨le_rfl, hε.1.le⟩
    change B (f (c * 0)) = A 0 at h
    rw [mul_zero, hBzero] at h
    exact h.symm
  have hAlin (t : ℝ) : A t = t • A 1 := by
    have h := A.toAffineMap.apply_lineMap (0 : ℝ) 1 t
    change A (AffineMap.lineMap 0 1 t) = AffineMap.lineMap (A 0) (A 1) t at h
    simpa [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_module', hA0] using h
  let δ : ℝ := c * ε
  let d : F := c⁻¹ • A 1
  have hδ : 0 < δ := mul_pos hc hε.1
  have hδc : δ ≤ c := mul_le_of_le_one_right hc.le hε.2
  have hδ1 : δ < 1 := by linarith
  have hδB : MapsTo f (Icc 0 δ) B.source :=
    fun _ ht => hfB ⟨ht.1, ht.2.trans hδc⟩
  have hformula (t : ℝ) (ht : t ∈ Icc 0 δ) : B (f t) = t • d := by
    have htε : t / c ∈ Icc (0 : ℝ) ε :=
      ⟨div_nonneg ht.1 hc.le, (div_le_iff₀ hc).mpr (by
        simpa only [δ, mul_comm] using ht.2)⟩
    have h := hA htε
    change B (f (c * (t / c))) = A (t / c) at h
    rw [mul_div_cancel₀ _ hc.ne', hAlin] at h
    simpa only [d, smul_smul, div_eq_mul_inv] using h
  have hd : d ≠ 0 := by
    intro hd0
    have hval : B (f δ) = B (f 0) := by
      rw [hformula δ ⟨hδ.le, le_rfl⟩, hd0, smul_zero, hBzero]
    have heq := hi ⟨hδ.le, hδ1.le⟩ ⟨le_rfl, zero_le_one⟩
      (B.injOn (hδB ⟨hδ.le, le_rfl⟩) hxB hval)
    exact hδ.ne' heq
  exact ⟨d, hd, δ, ⟨hδ, hδ1⟩, hδB, hformula⟩

end Geometry
