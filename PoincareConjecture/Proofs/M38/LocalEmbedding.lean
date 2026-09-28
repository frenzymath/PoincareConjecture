import PoincareConjecture.Proofs.M38.EventSlices
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)


theorem local_embed_openEmbedding :
    Topology.IsOpenEmbedding ((F.event T hT).local_embed i) :=
  ((F.event T hT).local_result i).metric.isOpenEmbedding_of_injective_pullback_eq
    (F.metric T) ((F.event T hT).local_embed_smooth i)
    ((F.event T hT).local_embed_injective i) ((F.event T hT).local_metric i)



noncomputable def localEmbedInverse : (F.slice T).carrier →
    ((F.event T hT).local_result i).output.carrier := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact Function.invFun ((F.event T hT).local_embed i)


theorem local_embed_left_inverse :
    Function.LeftInverse (localEmbedInverse F T hT i) ((F.event T hT).local_embed i) := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact Function.leftInverse_invFun ((F.event T hT).local_embed_injective i)


theorem local_embed_right_inverse :
    Set.LeftInvOn ((F.event T hT).local_embed i) (localEmbedInverse F T hT i)
      (Set.range ((F.event T hT).local_embed i)) := by
  rintro _ ⟨x, rfl⟩
  exact congrArg ((F.event T hT).local_embed i) (local_embed_left_inverse F T hT i x)



theorem local_embed_inverse_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (localEmbedInverse F T hT i)
      (Set.range ((F.event T hT).local_embed i)) := by
  let : Nonempty ((F.event T hT).local_result i).output.carrier :=
    ⟨((F.event T hT).local_result i).tip⟩
  exact ((F.event T hT).local_result i).metric.contMDiffOn_invFun_of_injective_pullback_eq
    (F.metric T) ((F.event T hT).local_embed_smooth i)
    ((F.event T hT).local_embed_injective i) ((F.event T hT).local_metric i)

end PoincareConjecture.M38
