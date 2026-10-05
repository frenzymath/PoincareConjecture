import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RadialLoops

/-!
# Circle values determine the intrinsic tangent

Equal circle values do not identify the stored extension records. They do
identify the intrinsic tangents: the radialized extensions agree away from
zero and have the original tangents. This gives endpoint correction in the
C1 topology. Source: MT's loop-space convention, pp. 429-430.
-/

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareMT

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Equal circle values give equal intrinsic tangents, while leaving the
stored extensions distinct. Source: MT's C1 loop convention, pp. 429-430. -/
theorem m59Loop_tangent_eq_of_values
    {gamma delta : C1FreeLoopSpace (M := M)} (h : ∀ z, gamma z = delta z)
    (z : LoopCircle) : c1LoopTangent gamma z = c1LoopTangent delta z := by
  rw [← m59RadialLoop_tangent gamma z, ← m59RadialLoop_tangent delta z]
  apply TotalSpace.ext
  · exact (m59RadialLoop_apply gamma z).trans ((h z).trans (m59RadialLoop_apply delta z).symm)
  · apply heq_of_eq
    have hext : (gamma.extension ∘ Proofs.M58.radialNormalization) =ᶠ[𝓝 z.val]
        (delta.extension ∘ Proofs.M58.radialNormalization) := by
      filter_upwards [isOpen_loopAnnulus.mem_nhds (loopCircle_mem_annulus z)] with w hw
      have hw0 : w ≠ 0 := by
        intro hzero
        have hp := hw.1
        norm_num [hzero] at hp
      let w' : LoopCircle :=
        ⟨Proofs.M58.radialNormalization w, Proofs.M58.norm_radialNormalization hw0⟩
      exact (gamma.boundary w').trans ((h w').trans (delta.boundary w').symm)
    exact congrArg (fun L : LoopPlane →L[ℝ] LoopAmbient => L (loopCircleTangent z))
      (hext.mfderiv_eq (I := 𝓡 2) (I' := 𝓡 3))

/-- Replacing only the stored extensions preserves continuity of a map
already continuous in the C1 topology. Source: MT, pp. 429-430. -/
theorem continuous_of_loop_values_eq {X : Type v} [TopologicalSpace X]
    {f g : X → C1FreeLoopSpace (M := M)} (hg : Continuous g)
    (hvalues : ∀ x z, f x z = g x z) : Continuous f :=
  continuous_of_loop_firstJet_eq hg hvalues
    (fun x z => m59Loop_tangent_eq_of_values (hvalues x) z)

end PoincareMT
