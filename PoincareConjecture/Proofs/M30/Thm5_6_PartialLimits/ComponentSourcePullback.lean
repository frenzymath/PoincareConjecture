import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.BasedComponent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold




theorem exists_component_source_pullback
    (C : GeneralizedSliceCarrier.{u}) (p : C.carrier)
    (g : RiemannianMetric 3 C.carrier) (U : TopologicalSpace.Opens C.carrier)
    {J : Set ℝ} (F : RicciFlow 3 U J)
    (hterminal : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = g.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    (f : Y → (basedSliceCarrier C p).carrier)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (himage : ∀ x, (f x).val ∈ U) :
    let e : Y → U := fun x => ⟨(f x).val, himage x⟩
    ∃ G : RicciFlow 3 Y J,
      (∀ (t : ℝ) (x : Y) (v w : TangentSpace (𝓡 3) x),
        (G.metric t).inner x v w = (F.metric t).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w)) ∧
      (∀ (x : Y) (v w : TangentSpace (𝓡 3) x),
        (G.metric 0).inner x v w = (basedSliceMetric C p g).inner (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w)) ∧
      ∀ (m : ℕ) (t : ℝ) (x : Y),
        (G.connection t).curvatureDerivativeNorm m x =
          (F.connection t).curvatureDerivativeNorm m (e x) := by
  intro e
  let i : (basedSliceCarrier C p).carrier → C.carrier := Subtype.val
  have hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ i :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) _
  have hfambient : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (i ∘ f) :=
    fun x => (hf x).comp (𝓡 3) C.carrier (hi (f x))
  have hU : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → C.carrier) :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
    intro x
    have hix := hU (e x)
    apply ((hfambient x).comp (𝓡 3) U
      hix.localInverse_isLocalDiffeomorphAt).congr_of_eventuallyEq
    filter_upwards [(hfambient x).contMDiffAt.continuousAt.preimage_mem_nhds
      (hix.localInverse.open_source.mem_nhds hix.localInverse_mem_source)] with y hy
    exact Subtype.ext (hix.localInverse_right_inv hy).symm
  let G := F.pullbackWithConnection e he
    (fun t => ((F.metric t).pullbackOfLocalDiffeomorph e he).leviCivitaData)
  have hmetric (t : ℝ) (x : Y) (v w : TangentSpace (𝓡 3) x) :
      (G.metric t).inner x v w = (F.metric t).inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := rfl
  refine ⟨G, hmetric, ?_, ?_⟩
  · intro x v w
    rw [hmetric, hterminal, basedSliceMetric_inner]
    have hderiv :
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (e x)).comp
            (mfderiv (𝓡 3) (𝓡 3) e x) =
          (mfderiv (𝓡 3) (𝓡 3) i (f x)).comp (mfderiv (𝓡 3) (𝓡 3) f x) :=
      (mfderiv_comp x ((hU (e x)).mdifferentiableAt (by simp))
        ((he x).mdifferentiableAt (by simp))).symm.trans
          (mfderiv_comp x ((hi (f x)).mdifferentiableAt (by simp))
            ((hf x).mdifferentiableAt (by simp)))
    exact congrArg₂ (fun a b => g.inner (f x).val a b)
      (congrArg (fun L => L v) hderiv) (congrArg (fun L => L w) hderiv)
  · intro m t x
    exact (G.connection t).curvatureDerivativeNorm_eq_pullback (F.connection t)
      isOpen_univ he.contMDiff.contMDiffOn
      (fun y _ => ⟨he.mfderivToContinuousLinearEquiv (by simp) y, rfl⟩)
      (fun y _ v w => hmetric t y v w) m (mem_univ x)

end PoincareConjecture.M30
