import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
    (F : BasedFlow n T' T C) (G : BasedFlow n T' T D)
    {U : Set C.carrier}

noncomputable def of_spatial
    (hU : @IsOpen C.carrier C.topologicalSpace U) (f : C.carrier → D.carrier)
    (hemb : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      Topology.IsOpenEmbedding (fun x : U => f x))
    (hf : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U)
    (I : Set ℝ) : SmoothSpacetimeEmbedding F G (I ×ˢ U) := by
  classical
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let g : D.carrier → C.carrier := fun y =>
    if h : U.Nonempty then
      letI : Nonempty U := h.to_subtype
      (Function.invFun (fun x : U => f x) y : U)
    else F.base
  have hleft : ∀ x ∈ U, g (f x) = x := by
    intro x hx
    let : Nonempty U := ⟨⟨x, hx⟩⟩
    dsimp only [g]
    rw [dif_pos ⟨x, hx⟩]
    exact congrArg Subtype.val (Function.leftInverse_invFun hemb.injective ⟨x, hx⟩)
  have hgsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ g (f '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    apply Poincare.contMDiffAt_of_local_left_inverse (hf ⟨x, hx⟩).contMDiffAt
      ((hf ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hleft z hz
  refine
    { toFun := fun p => (p.1, f p.2)
      time_preserving := fun _ _ => rfl
      injective_on := ?_
      inverse := fun p => (p.1, g p.2)
      left_inverse := ?_
      right_inverse := ?_
      smooth_on := ?_
      smooth_inverse_on := ?_
      vector_field_compatible := ?_ }
  · intro p hp q hq hpq
    refine Prod.ext (congrArg (fun y : ℝ × D.carrier => y.1) hpq) ?_
    exact congrArg Subtype.val (hemb.injective
      (show f (⟨p.2, hp.2⟩ : U) = f (⟨q.2, hq.2⟩ : U) from
        congrArg Prod.snd hpq))
  · intro p hp
    exact Prod.ext rfl (hleft p.2 hp.2)
  · rintro _ ⟨p, hp, rfl⟩
    exact Prod.ext rfl (congrArg f (hleft p.2 hp.2))
  · have hfsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U :=
      fun x hx => (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt
    exact contMDiffOn_fst.prodMk
      (hfsmooth.comp contMDiffOn_snd (fun _ hp => hp.2))
  · apply contMDiffOn_fst.prodMk
    apply hgsmooth.comp contMDiffOn_snd
    rintro _ ⟨p, hp, rfl⟩
    exact mem_image_of_mem f hp.2
  · dsimp only
    intro t x
    simp only [F.spacetimeVectorField_spatial_zero,
      G.spacetimeVectorField_spatial_zero, mfderiv_const,
      zero_apply, map_zero, add_zero]

@[simp] theorem of_spatial_apply
    (hU : @IsOpen C.carrier C.topologicalSpace U) (f : C.carrier → D.carrier)
    (hemb : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      Topology.IsOpenEmbedding (fun x : U => f x))
    (hf : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U)
    (I : Set ℝ) (t : ℝ) (x : C.carrier) :
    (of_spatial F G hU f hemb hf I).toFun (t, x) = (t, f x) := rfl

theorem pullbackInnerValue_of_spatial
    (hU : @IsOpen C.carrier C.topologicalSpace U) (f : C.carrier → D.carrier)
    (hemb : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      Topology.IsOpenEmbedding (fun x : U => f x))
    (hf : letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : TopologicalSpace D.carrier := D.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U)
    (I : Set ℝ) (t : ℝ) (x : C.carrier) (v w : C.tangent x) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    pullbackInnerValue F G (of_spatial F G hU f hemb hf I) t x v w =
      (G.flow.metric t).inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) := rfl

end PoincareConjecture.SmoothSpacetimeEmbedding
