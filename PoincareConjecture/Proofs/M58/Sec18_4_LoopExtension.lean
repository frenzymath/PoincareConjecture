import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import PoincareConjecture.Proofs.M58.Mathlib.RadialNormalization
import PoincareConjecture.Proofs.M58.Mathlib.LocalTangentMap
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

universe u

namespace PoincareConjecture.Proofs.M58

theorem isOpen_loopAnnulus : IsOpen loopAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem loopCircle_mem_annulus (z : LoopCircle) : z.val ∈ loopAnnulus := by
  change 1 / 2 < ‖z.val‖ ∧ ‖z.val‖ < 2
  rw [z.property]
  norm_num

theorem continuous_loopCircleTangent : Continuous loopCircleTangent := by
  change Continuous (fun z : LoopCircle => WithLp.toLp 2 ![-z.val 1, z.val 0])
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((PiLp.continuous_apply 2 _ 1).comp continuous_subtype_val).neg
  · exact (PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val

theorem inner_loopCircleTangent (z : LoopCircle) :
    ⟪z.val, loopCircleTangent z⟫ = 0 := by
  simp [loopCircleTangent, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem mfderiv_radialNormalization_loopCircleTangent (z : LoopCircle) :
    mfderiv (𝓡 2) (𝓡 2) radialNormalization z.val (loopCircleTangent z) =
      loopCircleTangent z := by
  simpa +instances only [mfderiv_eq_fderiv] using!
    fderiv_radialNormalization_tangent z.property (inner_loopCircleTangent z)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M]

theorem contMDiffAt_loop_extension {F : LoopPlane → M}
    (hF : ContMDiffOn (𝓡 2) (𝓡 3) 1 F loopAnnulus) (z : LoopCircle) :
    ContMDiffAt (𝓡 2) (𝓡 3) 1 F z.val :=
  (hF _ (loopCircle_mem_annulus z)).contMDiffAt
    (isOpen_loopAnnulus.mem_nhds (loopCircle_mem_annulus z))

theorem continuous_loop_restriction {F : LoopPlane → M}
    (hF : ContMDiffOn (𝓡 2) (𝓡 3) 1 F loopAnnulus) :
    Continuous (fun z : LoopCircle => F z.val) :=
  continuous_iff_continuousAt.mpr fun z =>
    (contMDiffAt_loop_extension hF z).continuousAt.comp continuous_subtype_val.continuousAt

variable [IsManifold (𝓡 3) ∞ M]

theorem continuous_loop_restriction_tangent {F : LoopPlane → M}
    (hF : ContMDiffOn (𝓡 2) (𝓡 3) 1 F loopAnnulus) :
    Continuous (fun z : LoopCircle =>
      (⟨F z.val, mfderiv (𝓡 2) (𝓡 3) F z.val (loopCircleTangent z)⟩ :
        TangentBundle (𝓡 3) M)) := by
  have hsection : Continuous (fun z : LoopCircle =>
      (⟨z.val, loopCircleTangent z⟩ : TangentBundle (𝓡 2) LoopPlane)) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_subtype_val.prodMk continuous_loopCircleTangent)
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (continuousAt_tangentMap_of_contMDiffAt
    (contMDiffAt_loop_extension hF z)).comp hsection.continuousAt

noncomputable def loopOfExtension (F : LoopPlane → M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 3) 1 F loopAnnulus) :
    C1FreeLoopSpace (M := M) where
  toFun z := F z.val
  extension := F
  boundary _ := rfl
  regularity := hF
  continuous := continuous_loop_restriction hF
  tangent_continuous := continuous_loop_restriction_tangent hF

theorem contMDiffAt_radial_extension (γ : C1FreeLoopSpace (M := M))
    {z : LoopPlane} (hz : z ≠ 0) :
    ContMDiffAt (𝓡 2) (𝓡 3) 1 (γ.extension ∘ radialNormalization) z := by
  have hnorm := norm_radialNormalization hz
  have hrad : ContMDiffAt (𝓡 2) (𝓡 2) 1 radialNormalization z :=
    (contDiffAt_radialNormalization hz).contMDiffAt.of_le (by simp)
  exact (contMDiffAt_loop_extension γ.regularity ⟨radialNormalization z, hnorm⟩).comp z hrad

theorem contMDiffOn_radial_extension (γ : C1FreeLoopSpace (M := M)) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1
      (γ.extension ∘ radialNormalization) loopAnnulus := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    have hpos := hz.1
    norm_num [h] at hpos
  exact (contMDiffAt_radial_extension γ hz0).contMDiffWithinAt

theorem mfderiv_radial_extension (γ : C1FreeLoopSpace (M := M)) (z : LoopCircle) :
    mfderiv (𝓡 2) (𝓡 3) (γ.extension ∘ radialNormalization) z.val
        (loopCircleTangent z) =
      mfderiv (𝓡 2) (𝓡 3) γ.extension z.val (loopCircleTangent z) := by
  have hz0 : z.val ≠ 0 := by
    intro h
    simpa [h] using z.property
  have hrad : MDifferentiableAt (𝓡 2) (𝓡 2) radialNormalization z.val :=
    (contDiffAt_radialNormalization hz0).contMDiffAt.mdifferentiableAt (by simp)
  have hF : MDifferentiableAt (𝓡 2) (𝓡 3) γ.extension
      (radialNormalization z.val) := by
    rw [radialNormalization_of_norm_eq_one z.property]
    exact (contMDiffAt_loop_extension γ.regularity z).mdifferentiableAt one_ne_zero
  erw [mfderiv_comp_apply _ hF hrad, mfderiv_radialNormalization_loopCircleTangent,
    radialNormalization_of_norm_eq_one z.property]

end PoincareConjecture.Proofs.M58
