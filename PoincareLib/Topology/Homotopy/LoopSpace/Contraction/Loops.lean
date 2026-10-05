import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Extension

/-!
# The local contraction acting on C1 loops

Morgan--Tian Lemma 18.27, printed p. 434, contracts a family through small
disks. This file checks the canonical action in the contract's intrinsic
C1 topology, using radialized extensions and the derivative of the contraction.
Exact endpoint representatives are handled separately. See the task's
next-loop-action derivation for the quantifiers and bundled derivative formula.
-/

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A contraction smooth along the loop gives a C1 radialized extension.
Source: the C1 family construction in MT Lemma 18.27, printed p. 434. -/
theorem contMDiffOn_contraction_loop (C : ℝ × (M × M) → M)
    (t : ℝ) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z)) :
    ContMDiffOn (𝓡 2) (𝓡 3) 1
      (fun w => C (t, p, γ.extension (radialNormalization w))) loopAnnulus := by
  intro w hw
  have hw0 : w ≠ 0 := by
    intro h
    have hpos := hw.1
    norm_num [h] at hpos
  let z : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
  have hγ : ContMDiffAt (𝓡 2) (𝓡 3) 1 (γ.extension ∘ radialNormalization) w :=
    (contMDiffOn_radial_extension γ w hw).contMDiffAt (isOpen_loopAnnulus.mem_nhds hw)
  exact ((hC z).comp_of_eq
    (contMDiffAt_const.prodMk (contMDiffAt_const.prodMk hγ)) (by
      change (t, p, γ.extension z.val) = (t, p, γ z)
      rw [γ.boundary])).contMDiffWithinAt

/-- The canonical loop under a local contraction, with a radialized stored
extension. Source: MT Lemma 18.27, p. 434, next-loop-action derivation. -/
noncomputable def contractionLoop (C : ℝ × (M × M) → M)
    (t : ℝ) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z)) :
    C1FreeLoopSpace (M := M) :=
  loopOfExtension (fun w => C (t, p, γ.extension (radialNormalization w)))
    (contMDiffOn_contraction_loop C t p γ hC)

/-- Circle values of the canonical contracted loop. Source:
MT Lemma 18.27, printed p. 434. -/
theorem contractionLoop_apply (C : ℝ × (M × M) → M)
    (t : ℝ) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z))
    (z : LoopCircle) : contractionLoop C t p γ hC z = C (t, p, γ z) := by
  change C (t, p, γ.extension (radialNormalization z.val)) = _
  rw [radialNormalization_of_norm_eq_one z.property, γ.boundary]

/-- Intrinsic derivative of the canonical contracted extension. Source:
MT Lemma 18.27, p. 434, next-loop-action derivative calculation. -/
theorem mfderiv_contraction_loop (C : ℝ × (M × M) → M)
    (t : ℝ) (p : M) (γ : C1FreeLoopSpace (M := M)) (z : LoopCircle)
    (hC : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
      (t, p, γ z)) :
    mfderiv (𝓡 2) (𝓡 3)
        (fun w => C (t, p, γ.extension (radialNormalization w))) z.val
        (loopCircleTangent z) =
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, p, γ z)
        (0, 0, mfderiv (𝓡 2) (𝓡 3) γ.extension z.val (loopCircleTangent z)) := by
  have hγ : MDifferentiableAt (𝓡 2) (𝓡 3)
      (γ.extension ∘ radialNormalization) z.val :=
    (contMDiffAt_loop_extension (contMDiffOn_radial_extension γ) z).mdifferentiableAt
      one_ne_zero
  have hinput : MDifferentiableAt (𝓡 2)
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3)))
      (fun w => (t, p, γ.extension (radialNormalization w))) z.val :=
    mdifferentiableAt_const.prodMk (mdifferentiableAt_const.prodMk hγ)
  have heq : (t, p, γ.extension (radialNormalization z.val)) = (t, p, γ z) := by
    rw [radialNormalization_of_norm_eq_one z.property, γ.boundary]
  have hchain := mfderiv_comp_apply_of_eq z.val (hC.mdifferentiableAt one_ne_zero)
    hinput heq (loopCircleTangent z)
  erw [mfderiv_prodMk mdifferentiableAt_const (mdifferentiableAt_const.prodMk hγ),
    mfderiv_prodMk mdifferentiableAt_const hγ] at hchain
  simp only [mfderiv_const] at hchain
  change mfderiv (𝓡 2) (𝓡 3)
      (fun w => C (t, p, γ.extension (radialNormalization w))) z.val
      (loopCircleTangent z) =
    mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C (t, p, γ z)
      (0, 0, mfderiv (𝓡 2) (𝓡 3) (γ.extension ∘ radialNormalization) z.val
        (loopCircleTangent z)) at hchain
  erw [mfderiv_radial_extension γ z] at hchain
  exact hchain

/-- The bundled derivative formula for the canonical contracted loop.
Source: the C1 continuity step in MT Lemma 18.27, printed p. 434. -/
theorem contractionLoop_tangent (C : ℝ × (M × M) → M)
    (t : ℝ) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (t, p, γ z))
    (z : LoopCircle) :
    c1LoopTangent (contractionLoop C t p γ hC) z =
      tangentMap (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        ⟨(t, p, γ z), (0, 0, (c1LoopTangent γ z).2)⟩ := by
  apply TotalSpace.ext
  · exact contractionLoop_apply C t p γ hC z
  · apply heq_of_eq
    exact mfderiv_contraction_loop C t p γ z (hC z)

end PoincareMT.LoopSpace
