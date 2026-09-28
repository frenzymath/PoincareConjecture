import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.CurvatureSupremum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import PoincareConjecture.Proofs.M04.LocalMetricComparison
import PoincareConjecture.Proofs.M15.Prop8_2_CylinderDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64_compact_flow_curvature_bound
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image
    (m64CurvatureSupremum_continuous_of_compact (F := F) hcompact)
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro t ht x
  exact (m64Curvature_le_supremum
    (m64CurvatureRange_bddAbove_of_compact hcompact ht) x).trans
      ((hK ⟨t, ht, rfl⟩).trans (le_max_left _ _))

theorem m64_flow_tangentNorm_time_comparison
    (F : RicciFlow n M (Icc a b)) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).tangentNorm x v ≤
      Real.exp ((n : ℝ) * K * |t - s|) * (F.metric s).tangentNorm x v := by
  rcases le_total s t with hst | hts
  · have h := (M04.tangentNorm_comparison_at_of_curvature_bound F hs ht hst hK x
      (fun tau htau => hcurv tau ⟨hs.1.trans htau.1, htau.2.trans ht.2⟩ x) v).2
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h
  · have h := (M04.tangentNorm_comparison_at_of_curvature_bound F ht hs hts hK x
      (fun tau htau => hcurv tau ⟨ht.1.trans htau.1, htau.2.trans hs.2⟩ x) v).1
    have hmul := mul_le_mul_of_nonneg_left h
      (Real.exp_pos ((n : ℝ) * K * (s - t))).le
    have he : Real.exp ((n : ℝ) * K * (s - t)) *
        Real.exp (-(n : ℝ) * K * (s - t)) = 1 := by
      rw [← Real.exp_add]
      rw [show (n : ℝ) * K * (s - t) + -(n : ℝ) * K * (s - t) = 0 by ring,
        Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at hmul
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hmul

theorem m64_flow_edist_time_comparison
    (F : RicciFlow n M (Icc a b)) {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x y : M) :
    (F.metric t).edist x y ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * K * |t - s|)) * (F.metric s).edist x y := by
  apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le
    (F.metric s) (F.metric t) (F := id) contMDiff_id (Real.exp_pos _)
  intro q v
  simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using
    m64_flow_tangentNorm_time_comparison F hK hcurv hs ht q v

theorem m64Annulus_transport_metric [T2Space M]
    (g h : RiemannianMetric n M) {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) {C : ℝ} (hC : 0 ≤ C)
    (hcompare : ∀ x y : M, h.edist x y ≤ ENNReal.ofReal C * g.edist x y) :
    ∃ B : M64Annulus h c0 c1, B.map = A.map := by
  have hLip : ∀ x y : m64AnnulusDomain,
      h.edist (A.map x) (A.map y) ≤
        ENNReal.ofReal (C * A.lipschitz_constant) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    calc
      _ ≤ ENNReal.ofReal C * g.edist (A.map x) (A.map y) := hcompare _ _
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal A.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖) :=
        by gcongr; exact A.lipschitz_on_domain x y
      _ = _ := by rw [ENNReal.ofReal_mul hC, mul_assoc]
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨B, hmap, _⟩ := m64Annulus_of_lipschitz h A.map A.continuous_on_domain
    A.periodic A.lower_boundary A.upper_boundary
    (mul_nonneg hC A.lipschitz_nonnegative) hLip hfinite
    (show m64AnnulusArea h A.map < m64AnnulusArea h A.map + 1 by linarith)
  exact ⟨B, hmap⟩

theorem m64Annulus_transport_time [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric s) c0 c1) :
    ∃ B : M64Annulus (F.metric t) c0 c1, B.map = A.map := by
  obtain ⟨K, hK, hcurv⟩ := m64_compact_flow_curvature_bound F hcompact
  exact m64Annulus_transport_metric (F.metric s) (F.metric t) A
    (Real.exp_pos _).le (m64_flow_edist_time_comparison F hK hcurv hs ht)

end PoincareConjecture
