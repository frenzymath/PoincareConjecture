import PoincareConjecture.Proofs.M10.TerminalUniqueness
import PoincareConjecture.Proofs.M10.MinimizingLifts
import PoincareConjecture.Proofs.M10.SliceDifferentiability
import PoincareConjecture.Proofs.M10.SliceSard










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem mem_regularImage_of_differentiable_noncritical_value
    (hL : LGeodesicTheory F T τmax) (hwindow : Icc (T - τmax) T ⊆ J)
    (G : LExponentialGeometry F T τmax p) {q : M} {τ : ℝ}
    (hτ : 0 < τ) (hmax : τ < τmax)
    (hd : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun x ↦ reducedLength F T p x τ) q)
    (hc : q ∉ (fun Z ↦ G.gamma Z τ) ''
      {Z | ¬ Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ)}) :
    (q, τ) ∈ G.regularImage := by
  obtain ⟨Z, hend, hmin, _⟩ := exists_minimizing_lift hL G q τ hτ hmax
  have hcrit (W : TangentSpace (𝓡 n) p) (hW : G.gamma W τ = q) :
      Function.Bijective (G.toLExponentialFamily.sliceDifferential W τ) := by
    by_contra hbad
    exact hc ⟨W, hbad, hW⟩
  have hcZ := hcrit Z hend
  have hl : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun x ↦ reducedLength F T p x τ) (G.gamma Z τ) := hend.symm ▸ hd
  have huniq : G.toLExponentialFamily.uniqueMinimizing Z τ := by
    refine ⟨hτ, hmax, hmin, ?_⟩
    intro path hstart hfinish hpath
    obtain ⟨W, hW, _⟩ := G.minimizers_lift τ hτ hmax path hstart hpath
    have hWend : G.gamma W τ = G.gamma Z τ :=
      (hW ⟨hτ.le, le_rfl⟩).symm.trans hfinish
    have hWpath : EqOn path.curve (G.path W τ hτ hmax).curve (Icc 0 τ) := by
      simpa only [G.path_eq] using hW
    have hminW := minimizing_of_eqOn hpath hWpath
    have hcompare := minimizing_noncritical_gamma_eqOn hL hwindow G Z W hτ hmax
      hmin hminW hWend.symm hl hcZ (hcrit W (hWend.trans hend))
    exact fun s hs ↦ (hW hs).trans (hcompare hs).symm
  have hsource : (Z, τ) ∈ G.regular_chart.source := by
    rw [G.regular_source]
    exact ⟨huniq, hcZ⟩
  have himage := G.regular_chart.map_source hsource
  rw [G.regular_forward, hend] at himage
  exact himage

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem regularImage_slice_complement_eq_zero
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    calibratedMetricVolume (F.metric (T - τ)) {q | (q, τ) ∉ G.regularImage} = 0 := by
  have hnd := reducedLength_slice_nondifferentiability_eq_zero
    hL hDifferential hwindow p hτ hmax
  have hcv := exponential_slice_criticalValues_eq_zero hL G hτ hmax
  apply measure_mono_null (t :=
    {q | ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun x ↦ reducedLength F T p x τ) q} ∪
      (fun Z ↦ G.gamma Z τ) ''
        {Z | ¬ Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ)})
    ?_ (measure_union_null hnd hcv)
  intro q hq
  by_contra hbad
  have hd : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (fun x ↦ reducedLength F T p x τ) q := by
    by_contra hndq
    exact hbad (Or.inl hndq)
  have hc : q ∉ (fun Z ↦ G.gamma Z τ) ''
      {Z | ¬ Function.Bijective (G.toLExponentialFamily.sliceDifferential Z τ)} :=
    fun hcvq ↦ hbad (Or.inr hcvq)
  exact hq (mem_regularImage_of_differentiable_noncritical_value hL hwindow G hτ hmax hd hc)

end PoincareConjecture.M10
