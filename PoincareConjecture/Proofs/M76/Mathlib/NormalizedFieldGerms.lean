import PoincareConjecture.Proofs.M76.Mathlib.NormalizedFieldExtension
import Mathlib.Topology.Separation.Regular










set_option autoImplicit false

open Set ContinuousLinearMap
open scoped Topology

variable {X E F : Type*} [TopologicalSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]




theorem ContinuousOn.exists_frame_extension_eventuallyEq
    {f : X → E →L[ℝ] F} {S V : Set X} (hf : ContinuousOn f V)
    (hS : IsClosed S) (hV : V ∈ 𝓝ˢ S) (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (hnorm : ∀ x ∈ V, Function.RightInverse J (f x)) :
    ∃ g : C(X, E →L[ℝ] F), (∀ x, Function.RightInverse J (g x)) ∧
      (g : X → E →L[ℝ] F) =ᶠ[𝓝ˢ S] f := by
  obtain ⟨O, hO, hSO, hOV⟩ := mem_nhdsSet_iff_exists.mp hV
  obtain ⟨D, hDS, hD, hDO⟩ := exists_mem_nhdsSet_isClosed_subset
    (hO.mem_nhdsSet.mpr hSO) hS
  let fD : C(D, E →L[ℝ] F) := ⟨fun x => f x, (hf.mono (hDO.trans hOV)).domRestrict⟩
  obtain ⟨g, hgn, hgeq⟩ := fD.exists_frame_extension hD J Q0 h0
    (fun x => hnorm x (hOV (hDO x.property)))
  refine ⟨g, hgn, ?_⟩
  filter_upwards [hDS] with x hx
  exact hgeq ⟨x, hx⟩
