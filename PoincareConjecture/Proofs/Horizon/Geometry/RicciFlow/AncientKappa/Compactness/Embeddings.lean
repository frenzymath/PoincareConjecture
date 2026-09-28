import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.NormalizedKappaSpacetimeEmbedding

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {U : Set target.carrier.carrier}

local instance : ConnectedSpace source.carrier.carrier := source.connectedSpace



noncomputable def of_spatial
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) :
    NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U) := by
  classical
  let g : source.carrier.carrier → target.carrier.carrier := fun y =>
    if h : U.Nonempty then
      letI : Nonempty U := h.to_subtype
      (Function.invFun (fun x : U => f x) y : U)
    else target.base
  have hf_inj : Function.Injective (fun x : U => f x) := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property hxy)
  have hleft : ∀ x ∈ U, g (f x) = x := by
    intro x hx
    let : Nonempty U := ⟨⟨x, hx⟩⟩
    dsimp only [g]
    rw [dif_pos ⟨x, hx⟩]
    exact congrArg Subtype.val (Function.leftInverse_invFun hf_inj ⟨x, hx⟩)
  have hgsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (f '' U) := by
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
      smooth_inverse_on := ?_ }
  · intro p hp q hq hpq
    exact Prod.ext (congrArg (fun y : ℝ × source.carrier.carrier => y.1) hpq)
      (hinj hp.2 hq.2 (congrArg Prod.snd hpq))
  · intro p hp
    exact Prod.ext rfl (hleft p.2 hp.2)
  · rintro _ ⟨p, hp, rfl⟩
    exact Prod.ext rfl (congrArg f (hleft p.2 hp.2))
  · have hfsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U :=
      fun x hx => (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt
    exact contMDiffOn_fst.prodMk
      (hfsmooth.comp contMDiffOn_snd (fun _ hp => hp.2))
  · apply contMDiffOn_fst.prodMk
    apply hgsmooth.comp contMDiffOn_snd
    rintro _ ⟨p, hp, rfl⟩
    exact mem_image_of_mem f hp.2

@[simp] theorem of_spatial_apply
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) (t : ℝ) (x : target.carrier.carrier) :
    (of_spatial hU f hinj hf J).toFun (t, x) = (t, f x) := rfl

@[simp] theorem of_spatial_inverse_time
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) (t : ℝ) (y : source.carrier.carrier) :
    ((of_spatial hU f hinj hf J).inverse (t, y)).1 = t := rfl

theorem of_spatial_time_independent
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) (s t : ℝ) (x : target.carrier.carrier) :
    ((of_spatial hU f hinj hf J).toFun (s, x)).2 =
      ((of_spatial hU f hinj hf J).toFun (t, x)).2 := rfl

theorem of_spatial_inverse_time_independent
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) (s t : ℝ) (y : source.carrier.carrier) :
    ((of_spatial hU f hinj hf J).inverse (s, y)).2 =
      ((of_spatial hU f hinj hf J).inverse (t, y)).2 := rfl

theorem of_spatial_base_preserving
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (hbase : f target.base = source.base) (J : Set ℝ) (t : ℝ) :
    (of_spatial hU f hinj hf J).toFun (t, target.base) = (t, source.base) :=
  congrArg (Prod.mk t) hbase


theorem of_spatial_toFun_timeDomain
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (I J : Set ℝ) :
    (of_spatial hU f hinj hf I).toFun = (of_spatial hU f hinj hf J).toFun := rfl

theorem of_spatial_inverse_timeDomain
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (I J : Set ℝ) :
    (of_spatial hU f hinj hf I).inverse = (of_spatial hU f hinj hf J).inverse := rfl


theorem pullbackInnerValue_of_spatial
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (J : Set ℝ) (t : ℝ) (x : target.carrier.carrier)
    (v w : target.carrier.tangent x) :
    normalizedKappaPullbackInnerValue (of_spatial hU f hinj hf J) t x v w =
      (source.flow.flow.metric t).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := rfl

theorem pullbackCoefficient_of_spatial_timeDomain
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (I J : Set ℝ) (q : target.carrier.carrier) (a b : Fin 3) :
    normalizedKappaPullbackCoefficient (of_spatial hU f hinj hf I) q a b =
      normalizedKappaPullbackCoefficient (of_spatial hU f hinj hf J) q a b := rfl


def restrict {domain domain' : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (h : domain' ⊆ domain) :
    NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain' where
  toFun := e.toFun
  time_preserving := e.time_preserving
  injective_on := e.injective_on.mono h
  inverse := e.inverse
  left_inverse := fun p hp => e.left_inverse p (h hp)
  right_inverse := fun q hq => e.right_inverse q (image_mono h hq)
  smooth_on := e.smooth_on.mono h
  smooth_inverse_on := e.smooth_inverse_on.mono (image_mono h)

@[simp] theorem restrict_toFun {domain domain' : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (h : domain' ⊆ domain) : (e.restrict h).toFun = e.toFun := rfl

@[simp] theorem restrict_inverse {domain domain' : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (h : domain' ⊆ domain) : (e.restrict h).inverse = e.inverse := rfl

@[simp] theorem restrict_of_spatial
    (hU : IsOpen U) (f : target.carrier.carrier → source.carrier.carrier)
    (hinj : InjOn f U) (hf : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    {I J : Set ℝ} (hIJ : I ⊆ J) :
    (of_spatial hU f hinj hf J).restrict (Set.prod_mono hIJ (Subset.refl U)) =
      of_spatial hU f hinj hf I := rfl

@[simp] theorem pullbackInnerValue_restrict
    {domain domain' : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (h : domain' ⊆ domain) (t : ℝ) (x : target.carrier.carrier)
    (v w : target.carrier.tangent x) :
    normalizedKappaPullbackInnerValue (e.restrict h) t x v w =
      normalizedKappaPullbackInnerValue e t x v w := rfl

@[simp] theorem pullbackCoefficient_restrict
    {domain domain' : Set (ℝ × target.carrier.carrier)}
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) domain)
    (h : domain' ⊆ domain) (q : target.carrier.carrier) (a b : Fin 3)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) :
    normalizedKappaPullbackCoefficient (e.restrict h) q a b p =
      normalizedKappaPullbackCoefficient e q a b p := rfl

end PoincareConjecture.NormalizedKappaSpacetimeEmbedding
