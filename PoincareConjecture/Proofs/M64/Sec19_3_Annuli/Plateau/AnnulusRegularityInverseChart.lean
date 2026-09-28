import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRegularityCharts
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactWeakChain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

theorem m64MemLp_on_ball_of_continuous_closedBall
    {F : Type*} [NormedAddCommGroup F] {u : LoopPlane → F}
    {a : LoopPlane} {R : ℝ} (hu : ContinuousOn u (Metric.closedBall a R))
    (p : ℝ≥0∞) : MemLp u p (volume.restrict (Metric.ball a R)) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hu
  apply MemLp.of_bound ((hu.mono Metric.ball_subset_closedBall).aestronglyMeasurable
    Metric.isOpen_ball.measurableSet) C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64InverseChart_observed_weak_columns
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (b : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {W : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    {a : LoopPlane} {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : ContinuousOn u (Metric.closedBall a R))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (Metric.ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j) (fun p => u p j)
      (Metric.ball a R))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt (𝓡 n) b).target)
    (hrange : MapsTo u (Metric.closedBall a R) K) :
    let f := (extChartAt (𝓡 n) b).symm ∘ u
    let V := fun i p => fderiv ℝ (e ∘ (extChartAt (𝓡 n) b).symm) (u p) (W i p)
    MemLp (e ∘ f) 2 (volume.restrict (Metric.ball a r)) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict (Metric.ball a r))) ∧
      (∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => e (f p) j)
        (Metric.ball a r)) ∧
      ∀ i, ∀ᵐ p ∂volume.restrict (Metric.ball a r),
        V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)) := by
  let c := extChartAt (𝓡 n) b
  let F := e ∘ c.symm
  let f := c.symm ∘ u
  let V := fun i p => fderiv ℝ F (u p) (W i p)
  have htarget : IsOpen c.target := isOpen_extChartAt_target b
  have hF : ContDiffOn ℝ 1 F c.target := by
    intro y hy
    have hi := (contMDiffOn_extChartAt_symm (n := ∞) b _ hy).contMDiffAt
      (htarget.mem_nhds hy)
    exact (contMDiffAt_iff_contDiffAt.mp
      ((he _).comp y (hi.of_le (m := 1) (by simp)))).contDiffWithinAt
  have hmap : MapsTo u (Metric.closedBall a R) c.target := fun _ hp => hKt (hrange hp)
  have hFD : ContinuousOn (fderiv ℝ F) c.target :=
    hF.continuousOn_fderiv_of_isOpen htarget (by simp)
  have hDFu : ContinuousOn (fun p => fderiv ℝ F (u p)) (Metric.closedBall a R) :=
    hFD.comp hu hmap
  have hFu : ContinuousOn (e ∘ f) (Metric.closedBall a R) :=
    hF.continuousOn.comp hu hmap
  have hsub : Metric.ball a r ⊆ Metric.ball a R := Metric.ball_subset_ball hrR.le
  have hsmall : Metric.ball a r ⊆ Metric.closedBall a R :=
    hsub.trans Metric.ball_subset_closedBall
  have hFDiff (p : LoopPlane) (hp : p ∈ Metric.closedBall a R) :
      DifferentiableAt ℝ F (u p) :=
    (hF.contDiffAt (htarget.mem_nhds (hmap hp))).differentiableAt (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hDFu
  have hVfull (i : Fin 2) : MemLp (V i) 2 (volume.restrict (Metric.ball a R)) := by
    have hmeas : AEStronglyMeasurable (fun p => fderiv ℝ F (u p))
        (volume.restrict (Metric.ball a R)) :=
      (hDFu.mono Metric.ball_subset_closedBall).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet
    have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hmeas.prodMk (hW i).aestronglyMeasurable)
    apply ((hW i).norm.const_mul C).mono' hm
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hp
    exact (fderiv ℝ F (u p)).le_opNorm (W i p) |>.trans
      (mul_le_mul_of_nonneg_right (hC p (Metric.ball_subset_closedBall hp)) (norm_nonneg _))
  refine ⟨(m64MemLp_on_ball_of_continuous_closedBall hFu 2).mono_measure
    (Measure.restrict_mono hsub le_rfl),
    (fun i => (hVfull i).mono_measure (Measure.restrict_mono hsub le_rfl)), ?_, ?_⟩
  · intro i j
    let P := EuclideanSpace.proj (𝕜 := ℝ) j
    have hFP : ContDiffOn ℝ 1 (P ∘ F) c.target := P.contDiff.comp_contDiffOn hF
    have hwF := M60.suWeakPartial_comp_on_compact hr hrR
      (m64MemLp_on_ball_of_continuous_closedBall hu 4) hW hw htarget hK hKt hrange hFP i
    apply m64WeakPartialDeriv_ae_congr (Eventually.of_forall fun _ => rfl) ?_ hwF
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hp
    rw [fderiv_comp (u p) P.differentiableAt (hFDiff p (hsmall hp)), P.fderiv]
    rfl
  · intro i
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with p hp
    have hci := (contMDiffOn_extChartAt_symm (n := ∞) b _ (hmap (hsmall hp))).contMDiffAt
      (htarget.mem_nhds (hmap (hsmall hp)))
    refine ⟨mfderiv (𝓡 n) (𝓡 n) c.symm (u p) (W i p), ?_⟩
    have hd := mfderiv_comp (u p) ((he _).mdifferentiableAt (by simp))
      (hci.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact (congrArg (fun T => T (W i p)) hd).symm

end PoincareConjecture
