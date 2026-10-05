import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventSlices
import PoincareLib.Geometry.Riemannian.Coordinates.Transitions

/-!
# Smooth inverse for the actual local surgery embedding

The event's metric identity makes the tangent map invertible. Apply the
existing local inverse-function helpers to the same stored embedding,
without any selected M36 result or surjectivity assumption.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)

/-- The actual local embedding has open image and the inherited topology. -/
theorem local_embed_openEmbedding :
    Topology.IsOpenEmbedding ((F.event T hT).local_embed i) :=
  ((F.event T hT).local_result i).metric.isOpenEmbedding_of_injective_pullback_eq
    (F.metric T) ((F.event T hT).local_embed_smooth i)
    ((F.event T hT).local_embed_injective i) ((F.event T hT).local_metric i)

/-- The total chosen inverse has mathematical content only on the actual
embedding image; its fallback uses the supplied local tip. -/
noncomputable def localEmbedInverse : (F.slice T).carrier →
    ((F.event T hT).local_result i).output.carrier := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact Function.invFun ((F.event T hT).local_embed i)

/-- The chosen inverse recovers every point of the supplied local output. -/
theorem local_embed_left_inverse :
    Function.LeftInverse (localEmbedInverse F T hT i) ((F.event T hT).local_embed i) := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact Function.leftInverse_invFun ((F.event T hT).local_embed_injective i)

/-- It is also a right inverse precisely on the embedding image. -/
theorem local_embed_right_inverse :
    Set.LeftInvOn ((F.event T hT).local_embed i) (localEmbedInverse F T hT i)
      (Set.range ((F.event T hT).local_embed i)) := by
  rintro _ ⟨x, rfl⟩
  exact congrArg ((F.event T hT).local_embed i) (local_embed_left_inverse F T hT i x)

/-- The event's smoothness, injectivity and metric identity supply the
smooth inverse on the exact image used by the cap chart. -/
theorem local_embed_inverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (localEmbedInverse F T hT i)
      (Set.range ((F.event T hT).local_embed i)) := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact ((F.event T hT).local_result i).metric.contMDiffOn_invFun_of_injective_pullback_eq
    (F.metric T) ((F.event T hT).local_embed_smooth i)
    ((F.event T hT).local_embed_injective i) ((F.event T hT).local_metric i)

end PoincareMT.M38
