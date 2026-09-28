import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceRescaling
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakRescaling

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

def m64SourceAffine (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) : LoopPlane ≃ₜ LoopPlane :=
  (m64SourceScale s hs).toHomeomorph.trans (Homeomorph.addLeft a)

theorem m64SourceAffine_measurePreserving (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    MeasurePreserving (m64SourceAffine a s hs) volume volume :=
  (measurePreserving_add_left (volume : Measure LoopPlane) a).comp
    (m64SourceScale_measurePreserving s hs)

theorem m64SourceAffine_memLp {E : Type*} [NormedAddCommGroup E]
    {u : LoopPlane → E} {O : Set LoopPlane} {p : ℝ≥0∞}
    (hu : MemLp u p (volume.restrict O)) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    MemLp (u ∘ m64SourceAffine a s hs) p
      (volume.restrict (m64SourceAffine a s hs ⁻¹' O)) :=
  hu.comp_measurePreserving ((m64SourceAffine_measurePreserving a s hs).restrict_preimage_emb
    (m64SourceAffine a s hs).measurableEmbedding O)

theorem m64SourceAffine_ae {O : Set LoopPlane} {P : LoopPlane → Prop}
    (hP : ∀ᵐ x ∂volume.restrict O, P x) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    ∀ᵐ x ∂volume.restrict (m64SourceAffine a s hs ⁻¹' O),
      P (m64SourceAffine a s hs x) :=
  ((m64SourceAffine_measurePreserving a s hs).restrict_preimage_emb
    (m64SourceAffine a s hs).measurableEmbedding O).quasiMeasurePreserving.ae hP

theorem m64SourceAffine_weakPartial {O : Set LoopPlane} {u V : LoopPlane → ℝ}
    {i : Fin 2} (hw : HasWeakPartialDeriv i V u O)
    (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    HasWeakPartialDeriv i
      (fun z => m64SourceScaleFactor s i * V (m64SourceAffine a s hs z))
      (u ∘ m64SourceAffine a s hs) (m64SourceAffine a s hs ⁻¹' O) := by
  have ht := M60.suAffine_weakPartial hw a (show 0 < (1 : ℝ) by norm_num)
  simp only [one_mul, one_smul] at ht
  exact m64SourceScale_weakPartial ht s hs

theorem m64SourceAffine_dist_le (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    (x y : LoopPlane) :
    dist (m64SourceAffine a s hs x) (m64SourceAffine a s hs y) ≤
      ‖(m64SourceScale s hs).toContinuousLinearMap‖ * dist x y := by
  change dist (a + m64SourceScale s hs x) (a + m64SourceScale s hs y) ≤ _
  rw [dist_add_left, dist_eq_norm, ← map_sub, dist_eq_norm]
  exact (m64SourceScale s hs).toContinuousLinearMap.le_opNorm (x - y)

theorem m64SourceScale_factor_le_norm (s : ℝ) (hs : s ≠ 0) (i : Fin 2) :
    ‖m64SourceScaleFactor s i‖ ≤ ‖(m64SourceScale s hs).toContinuousLinearMap‖ := by
  have h := (m64SourceScale s hs).toContinuousLinearMap.le_opNorm
    (EuclideanSpace.single i 1)
  change ‖m64SourceScale s hs (EuclideanSpace.single i 1)‖ ≤ _ at h
  simpa only [m64SourceScale_basis, norm_smul, PiLp.norm_single,
    norm_one, mul_one] using h

end PoincareConjecture
