import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation



theorem m64SeamRepresentative_eq_extend {M : Type*} (F : LoopPlane → M)
    (hshift : ∀ p ∈ m64AnnulusSeamLeft, F (v + p) = F p) :
    EqOn (m64AnnulusSeamExtend F) F O := by
  intro p hp
  by_cases hn : p 0 < 0
  · have hpL := (m64AnnulusSeamLeft_coordinates p).mpr ⟨hp.1, hn, hp.2.2⟩
    exact (m64AnnulusSeamExtend_left F hpL).trans (hshift p hpL)
  · simp only [m64AnnulusSeamExtend, if_neg hn]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem M64ObservedWeakAnnulus.exists_seam_local_chart_columns
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : Continuous e) (hread : M60.SUChartReadable (n := n) e)
    (hA : ContinuousOn (m64AnnulusSeamExtend A.map) O) {a : LoopPlane} (ha : a ∈ O) :
    ∃ (b : M) (L : E →L[ℝ] EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R ∧ R < curvePeriod ∧ Metric.closedBall a R ⊆ O ∧
      (∀ p ∈ Metric.closedBall a R,
        m64AnnulusSeamExtend A.map p ∈ (extChartAt (𝓡 n) b).source ∧
          L (e (m64AnnulusSeamExtend A.map p)) =
            extChartAt (𝓡 n) b (m64AnnulusSeamExtend A.map p)) ∧
      ContinuousOn (fun p => L (e (m64AnnulusSeamExtend A.map p))) (Metric.closedBall a R) ∧
      MemLp (fun p => L (e (m64AnnulusSeamExtend A.map p))) 2
        (volume.restrict (Metric.ball a R)) ∧
      (∀ i, MemLp (fun p => L (m64AnnulusSeamExtend (A.column i : LoopPlane → E) p)) 2
        (volume.restrict (Metric.ball a R))) ∧
      ∀ i j, HasWeakPartialDeriv i
        (fun p => L (m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) j)
        (fun p => L (e (m64AnnulusSeamExtend A.map p)) j) (Metric.ball a R) := by
  let F := m64AnnulusSeamExtend A.map
  obtain ⟨b, hb, L, hL⟩ := hread (F a)
  have hAa : ContinuousAt F a := hA.continuousAt (m64AnnulusSeamDomain_isOpen.mem_nhds ha)
  have hnear : {p | F p ∈ (extChartAt (𝓡 n) b).source ∧
      L (e (F p)) = extChartAt (𝓡 n) b (F p)} ∈ 𝓝 a :=
    inter_mem (hAa.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb))
      (hL.comp_tendsto hAa)
  obtain ⟨R0, hR0, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (m64AnnulusSeamDomain_isOpen.mem_nhds ha) hnear)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let R := min R0 (curvePeriod / 2)
  have hR : 0 < R := lt_min hR0 (half_pos hP)
  have hRP : R < curvePeriod := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hP)
  have hsmall : Metric.closedBall a R ⊆ Metric.closedBall a R0 :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hRO : Metric.closedBall a R ⊆ O := fun p hp => (hball (hsmall hp)).1
  have hBO : Metric.ball a R ⊆ O := Metric.ball_subset_closedBall.trans hRO
  refine ⟨b, L, R, hR, hRP, hRO, (fun p hp => (hball (hsmall hp)).2), ?_, ?_, ?_, ?_⟩
  · exact (L.continuous.comp_continuousOn (he.comp_continuousOn hA)).mono hRO
  · exact (L.comp_memLp' A.seam_extension_memLp.1).mono_measure (Measure.restrict_mono hBO le_rfl)
  · intro i
    exact (L.comp_memLp' (A.seam_extension_memLp.2 i)).mono_measure
      (Measure.restrict_mono hBO le_rfl)
  · intro i j
    exact (m64WeakPartial_comp_linear A.seam_extension_memLp.1 (A.seam_extension_memLp.2 i)
      (A.seam_extension_weak_partial i) L j).restrict Metric.isOpen_ball hBO

end PoincareConjecture
