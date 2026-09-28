import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ZeroDimensionalBase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.NonemptyEvolution
import PoincareConjecture.Statements.M64Annulus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem annulus_area_eq_zero_of_dimension_lt_two
    (hn : n < 2) (g : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) : A.area = 0 := by
  have hdet (z : LoopPlane) : Matrix.det (m60AreaGram g A.map z) = 0 := by
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (A.map z)) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) (A.map z)
    by_contra hnonzero
    have hdim := ((m60AreaGram_det_ne_zero_iff g A.map z).mp hnonzero).fintype_card_le_finrank
    have hfinrank : Module.finrank ℝ (TangentSpace (𝓡 n) (A.map z)) = n := by
      rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
      simp
    rw [Fintype.card_fin, hfinrank] at hdim
    omega
  have hdensity : m60AreaDensity g A.map = fun _ => (0 : ℝ) := by
    funext z
    simp only [m60AreaDensity, hdet z, max_self, Real.sqrt_zero]
  unfold M64Annulus.area m64AnnulusArea
  rw [hdensity]
  exact MeasureTheory.integral_zero _ _

variable [T2Space M] [CompactSpace M] {a b : ℝ}
  {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem annulusFlowConclusion_of_dimension_zero
    (hn : n = 0) (G : M63AmbientGeometry F) (h : 0 < circumference)
    (c0 c1 : ℝ → ℝ → (G.product circumference h).charts.Point)
    (hc0 : M63C2ShrinkingCurveOn (G.product circumference h).flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn (G.product circumference h).flow c1 (Icc a b))
    (A0 : M64Annulus ((G.product circumference h).flow.metric a)
      (fun x => c0 x a) (fun x => c1 x a)) :
    M64AnnulusFlowConclusion G h c0 c1 := by
  have hnonempty := m64AnnulusFlow_nonempty_of_initial isCompact_univ h
    (G.product circumference h) hc0 hc1 A0
  have hzero (t : ℝ) (ht : t ∈ Icc a b) :
      m64FlowAnnulusArea (G.product circumference h) c0 c1 t = 0 := by
    obtain ⟨A⟩ := hnonempty t ht
    have hA := annulus_area_eq_zero_of_dimension_lt_two (by omega : n + 1 < 2) _ A
    exact le_antisymm ((m64LeastAnnulusArea_le_annulus A).trans_eq hA)
      (m64LeastAnnulusArea_nonneg A)
  refine {
    nonempty := hnonempty
    bounded_below := fun _ _ => m64AnnulusAreaRange_bddBelow _ _ _
    nonnegative := fun t ht => by rw [hzero t ht]
    continuous := continuousOn_const.congr (fun t ht => hzero t ht)
    forward := ?_
    exponential := ?_ }
  · intro t ht eta heta
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < b - t :=
      nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr ht.2))
    filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hpos
    change 0 < s at hpos
    have hfuture : t + s ∈ Icc a b := ⟨by linarith [ht.1], by linarith⟩
    rw [hzero (t + s) hfuture, hzero t ⟨ht.1, ht.2.le⟩]
    simpa using heta.le
  · intro s t hs ht _
    rw [hzero t ht, hzero s hs, mul_zero]

theorem annulusEvolution_of_dimension_zero
    (hn : n = 0) (G : M63AmbientGeometry F) : M64AnnulusEvolution G := by
  refine {
    curvature_bounded := fun t ht =>
      m64CurvatureRange_bddAbove_of_compact (F := F) isCompact_univ ht
    curvature_nonnegative := fun t _ => ?_
    curvature_continuous := continuousOn_const.congr
      (fun t _ => curvatureSupremum_eq_zero_of_dimension_zero hn t)
    curves := fun circumference h c0 c1 hc0 hc1 _ _ _ _ A0 =>
      annulusFlowConclusion_of_dimension_zero hn G h c0 c1 hc0 hc1 A0 }
  rw [curvatureSupremum_eq_zero_of_dimension_zero hn t]

end PoincareConjecture.M64
