import PoincareConjecture.Proofs.M47.GeneralizedBridgeGeometry
import PoincareConjecture.Proofs.M33.GuardedCylinders

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W)

theorem regular_history_backward_cylinder_time
    {C : GeneralizedSliceCarrier.{u}} {t scale a : ℝ} {U : Set C.carrier}
    (ht : t ∈ H.generalized.interval)
    (e : SurgeryFlowCylinder F C t scale (Ioc a 0) U)
    (s : ℝ) (hs : s ∈ Ioc a 0) : t + s / scale ∈ H.generalized.interval := by
  rw [H.interval_eq]
  apply W.interval_connected.out W.zero_mem (H.interval_eq ▸ ht)
  refine ⟨F.time_domain_nonnegative (e.time_subset (mem_image_of_mem _ hs)), ?_⟩
  exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 e.scale_pos.le)

theorem exists_regular_history_backward_cylinder
    {C : GeneralizedSliceCarrier.{u}} {t scale a : ℝ} {U : Set C.carrier}
    (ht : t ∈ H.generalized.interval) (hU : IsOpen U)
    (e : SurgeryFlowCylinder F C t scale (Ioc a 0) U) :
    ∃ d : GeneralizedFlowCylinder H.generalized C t scale (Ioc a 0) U,
      (∀ s hs x, x ∈ U → H.history.forward (t + s / scale)
        (regular_history_backward_cylinder_time H ht e s hs) (d.forward s hs x) =
          e.forward s hs x) ∧
      (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
        d.pullbackInner s hs x v w = e.pullbackInner s hs x v w) :=
  H.cylinders_from_surgery C t scale (Ioc a 0) U hU
    (regular_history_backward_cylinder_time H ht e) e
    (fun _ hs => e.regular_image_Ioc hs)

variable {t origin scale : ℝ} (ht : t ∈ H.generalized.interval)
  {J : Set ℝ} (U : Set (F.slice t).carrier)
  (d : GeneralizedFlowCylinder H.generalized (F.slice t) origin scale J U)

noncomputable def regular_history_rebase_cylinder :
    GeneralizedFlowCylinder H.generalized (H.generalized.slice t) origin scale J
      (H.history.forward t ht ⁻¹' U) := by
  have hmaps : MapsTo (H.history.forward t ht) (H.history.forward t ht ⁻¹' U) U :=
    fun _ hx => hx
  have himage (s : ℝ) (hs : s ∈ J) :
      (d.forward s hs ∘ H.history.forward t ht) '' (H.history.forward t ht ⁻¹' U) ⊆
        d.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨H.history.forward t ht x, hx, rfl⟩
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ H.history.forward t ht
    inverse := fun s hs => H.history.inverse t ht ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp
      (H.history.forward_smooth t ht).contMDiffOn hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := ?_
    vertical_compatibility := fun s hs x hx => d.vertical_compatibility s hs _ hx
  }
  · intro s hs
    apply (H.history.inverse_smooth t ht).comp
      ((d.inverse_smooth s hs).mono (himage s hs))
    rintro _ ⟨x, hx, rfl⟩
    change d.inverse s hs (d.forward s hs (H.history.forward t ht x)) ∈
      range (H.history.forward t ht)
    rw [d.left_inverse s hs hx]
    exact mem_range_self x
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, H.history.left_inverse t ht x]
  · rintro s hs _ ⟨x, hx, rfl⟩
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs hx, H.history.left_inverse t ht x]
  · exact d.embedding.comp (Topology.IsEmbedding.id.prodMap
      ((H.history.forward_openEmbedding t ht).isEmbedding.restrict hmaps))

theorem regular_history_rebase_pullback (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) (x : (H.generalized.slice t).carrier)
    (hx : H.history.forward t ht x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (regular_history_rebase_cylinder H ht U d).pullbackInner s hs x v w =
      d.pullbackInner s hs (H.history.forward t ht x)
        (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) x w) := by
  have hd := ((d.forward_smooth s hs).mdifferentiableOn (by simp) _ hx).mdifferentiableAt
    (hU.mem_nhds hx)
  have hf := (H.history.forward_smooth t ht).mdifferentiable (by simp) x
  change scale * (H.generalized.metric (origin + s / scale)).inner _
    (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs ∘ H.history.forward t ht) x v)
    (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs ∘ H.history.forward t ht) x w) = _
  rw [mfderiv_comp x hd hf]
  rfl

end PoincareConjecture.M47
