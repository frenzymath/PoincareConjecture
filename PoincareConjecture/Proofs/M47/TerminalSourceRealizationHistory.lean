import PoincareConjecture.Proofs.M47.TerminalSourceRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem terminalSourceRealization_regular_history
    (P : M47Predecessors.{u}) {S : SurgeryFlowData.{u}}
    {W : M33RegularHistoryWindow S} (H : M33RegularHistoryData W)
    {C : GeneralizedSliceCarrier.{u}} {b Q τ : ℝ} (hτ : 0 < τ)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : GeneralizedFlowCylinder H.generalized C b Q (Icc (-τ) 0) U) :
    ∃ F : RicciFlow 3 U (Icc (-τ) 0),
      ∃ htime : ∀ s ∈ Icc (-τ) 0, b + s / Q ∈ H.generalized.interval,
      ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U),
        ((∀ v w : TangentSpace (𝓡 3) x,
          (F.metric s).inner x v w = e.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
          (F.connection s).scalarCurvature x =
            (H.generalized.connection (b + s / Q)).scalarCurvature
              (e.forward s hs x.val) / Q ∧
          (F.connection s).curvatureTensorNorm x =
            (H.generalized.connection (b + s / Q)).curvatureTensorNorm
              (e.forward s hs x.val) / Q) ∧
        ((∀ v w : TangentSpace (𝓡 3) x,
          (F.metric s).inner x v w = Q * (S.metric (b + s / Q)).inner
            (H.history.forward (b + s / Q) (htime s hs) (e.forward s hs x.val))
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U =>
              H.history.forward (b + s / Q) (htime s hs) (e.forward s hs y.val)) x v)
            (mfderiv (𝓡 3) (𝓡 3) (fun y : U =>
              H.history.forward (b + s / Q) (htime s hs) (e.forward s hs y.val)) x w)) ∧
          (F.connection s).scalarCurvature x =
            (S.connection (b + s / Q)).scalarCurvature
              (H.history.forward (b + s / Q) (htime s hs) (e.forward s hs x.val)) / Q ∧
          (F.connection s).curvatureTensorNorm x =
            (S.connection (b + s / Q)).curvatureTensorNorm
              (H.history.forward (b + s / Q) (htime s hs) (e.forward s hs x.val)) / Q) := by
  obtain ⟨F, hF⟩ := terminalSourceRealization_generalized P hτ U hne e
  have htime (s : ℝ) (hs : s ∈ Icc (-τ) 0) :
      b + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨e.forward s hs hne.choose⟩
  refine ⟨F, htime, ?_⟩
  intro s hs x
  refine ⟨hF s hs x, ?_, ?_, ?_⟩
  · intro v w
    have hf := (e.forward_smooth s hs x.val x.property).contMDiffAt
      (U.isOpen.mem_nhds x.property)
    have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → C.carrier) x :=
      contMDiff_subtype_val (n := ∞) x
    have hA := hf.comp x hi
    have hd₁ := mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))
    have hd₂ := mfderiv_comp x
      ((H.history.forward_smooth (b + s / Q) (htime s hs)).contMDiffAt.mdifferentiableAt
        (by simp)) (hA.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun y : U =>
      H.history.forward (b + s / Q) (htime s hs) (e.forward s hs y.val)) x = _ at hd₂
    rw [(hF s hs x).1 v w, hd₂, hd₁]
    exact congrArg (fun z : ℝ => Q * z)
      (H.history.metric_pullback (b + s / Q) (htime s hs) (e.forward s hs x.val)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))).symm
  · rw [(hF s hs x).2.1, H.scalar_pullback]
  · rw [(hF s hs x).2.2, H.curvature_norm_pullback]

end PoincareConjecture.M47
