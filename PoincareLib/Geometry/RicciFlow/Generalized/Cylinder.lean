import PoincareLib.Geometry.RicciFlow.Generalized.Basic

/-!
# Rescaled cylinders in generalized Ricci flows

Adapted from Mapher, `PoincareMT/Definitions/Ch11/BlowupLimits.lean`, commit
`4a6b36794e04c3fac86663910a73a924fed43f23`.
Declaration bodies are retained; only the required definition closure is imported.
See `references/ricci-flow/mapher/reviewed-bounded-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u

namespace PoincareMT

structure GeneralizedFlowCylinder (F : GeneralizedRicciFlowData.{u})
    (C : GeneralizedSliceCarrier.{u}) (origin scale : ℝ)
    (I : Set ℝ) (U : Set C.carrier) where
  scale_pos : 0 < scale
  forward : ∀ s : ℝ, s ∈ I → C.carrier → (F.slice (origin + s / scale)).carrier
  inverse : ∀ s : ℝ, s ∈ I →
    (F.slice (origin + s / scale)).carrier → C.carrier
  forward_smooth : ∀ s hs, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (forward s hs) U
  inverse_smooth : ∀ s hs,
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (inverse s hs) (forward s hs '' U)
  left_inverse : ∀ s hs, Set.LeftInvOn (inverse s hs) (forward s hs) U
  right_inverse : ∀ s hs,
    Set.LeftInvOn (forward s hs) (inverse s hs) (forward s hs '' U)
  embedding : Topology.IsEmbedding (fun p : I × U ↦
    (⟨origin + p.1.1 / scale, forward p.1.1 p.1.2 p.2.1⟩ : F.point))
  vertical_compatibility : ∀ (s : ℝ), s ∈ I → ∀ x, x ∈ U →
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s' hs', |s' - s| < δ → ∃ hb : origin + s' / scale ∈ (F.box b).interval,
        forward s' hs' x = (F.box b).forward (origin + s' / scale) hb y

noncomputable def GeneralizedFlowCylinder.pointMap {F : GeneralizedRicciFlowData}
    {C : GeneralizedSliceCarrier} {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier) : F.point :=
  ⟨origin + s / scale, e.forward s hs x⟩

noncomputable def GeneralizedFlowCylinder.pullbackInner
    {F : GeneralizedRicciFlowData} {C : GeneralizedSliceCarrier}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) : ℝ :=
  scale * (F.metric (origin + s / scale)).inner (e.forward s hs x)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w)

end PoincareMT

