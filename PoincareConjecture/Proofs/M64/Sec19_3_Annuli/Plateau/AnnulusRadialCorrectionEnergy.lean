import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCorrectionWeak












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture



theorem m64PlaneReflection_preimage_ball {a : LoopPlane} (ha : a 1 = 0) (r : ℝ) :
    m60PlaneReflection ⁻¹' ball a r = ball a r := by
  ext p
  simp only [mem_preimage, mem_ball]
  have hd := m60PlaneReflection.dist_map p a
  rw [m64PlaneReflection_fixed ha] at hd
  rw [hd]



theorem m64PlaneReflection_measurePreserving_ball {a : LoopPlane} (ha : a 1 = 0) (r : ℝ) :
    MeasurePreserving m60PlaneReflection (volume.restrict (ball a r))
      (volume.restrict (ball a r)) := by
  have h := m60PlaneReflection.measurePreserving.restrict_preimage_emb
    m60PlaneReflection.toHomeomorph.measurableEmbedding (ball a r)
  rwa [m64PlaneReflection_preimage_ball ha r] at h

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)



theorem m64RadialCorrect_column_energy_le
    {f h : LoopPlane → E} (hf : ContDiff ℝ 1 f) (hh : ContDiff ℝ 1 h)
    {a : LoopPlane} (ha : a 1 = 0) (r : ℝ) (i : Fin 2) :
    (∫ p in ball a r, ‖fderiv ℝ (m64RadialCorrect f h) p (EuclideanSpace.single i 1)‖ ^ 2) ≤
      6 * (∫ p in ball a r, ‖fderiv ℝ f p (EuclideanSpace.single i 1)‖ ^ 2) +
        3 * (∫ p in ball a r, ‖fderiv ℝ h p (EuclideanSpace.single i 1)‖ ^ 2) := by
  let Df := fun p => fderiv ℝ f p (EuclideanSpace.single i 1)
  let Dh := fun p => fderiv ℝ h p (EuclideanSpace.single i 1)
  let Dc := fun p => fderiv ℝ (m64RadialCorrect f h) p (EuclideanSpace.single i 1)
  have hfc : Continuous Df := (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hhc : Continuous Dh := (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfi : IntegrableOn (fun p => ‖Df p‖ ^ 2) (ball a r) volume :=
    (hfc.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  have hhi : IntegrableOn (fun p => ‖Dh p‖ ^ 2) (ball a r) volume :=
    (hhc.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  have hri : IntegrableOn (fun p => ‖Df (m60PlaneReflection p)‖ ^ 2) (ball a r) volume :=
    ((hfc.comp m60PlaneReflection.continuous).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall a r) |>.mono_set ball_subset_closedBall
  have hdc : MemLp Dc 2 (volume.restrict (ball a r)) :=
    (m64RadialCorrect_weak_data hf hh ha r).2.1 i
  have hci := (memLp_two_iff_integrable_sq_norm hdc.aestronglyMeasurable).mp hdc
  have hchange : (∫ p in ball a r, ‖Df (m60PlaneReflection p)‖ ^ 2) =
      ∫ p in ball a r, ‖Df p‖ ^ 2 :=
    (m64PlaneReflection_measurePreserving_ball ha r).integral_comp
      m60PlaneReflection.toHomeomorph.measurableEmbedding (fun p => ‖Df p‖ ^ 2)
  have hsum : Integrable (fun p => ‖Df p‖ ^ 2 + ‖Df (m60PlaneReflection p)‖ ^ 2)
      (volume.restrict (ball a r)) := by
    simpa +instances only [IntegrableOn, Pi.add_apply] using! hfi.add hri
  calc
    _ ≤ ∫ p in ball a r, 3 * (‖Df p‖ ^ 2 + ‖Df (m60PlaneReflection p)‖ ^ 2 + ‖Dh p‖ ^ 2) := by
      apply integral_mono_ae hci (((hfi.add hri).add hhi).const_mul 3)
      exact ae_restrict_of_ae (m64RadialCorrect_column_bound_ae
        (hf.differentiable (by simp)) (hh.differentiable (by simp)) i)
    _ = _ := by
      rw [integral_const_mul,
        integral_add (f := fun p => ‖Df p‖ ^ 2 + ‖Df (m60PlaneReflection p)‖ ^ 2)
          (g := fun p => ‖Dh p‖ ^ 2) hsum hhi,
        integral_add hfi hri, hchange]
      dsimp only [Df, Dh]
      ring

end PoincareConjecture
