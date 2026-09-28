import PoincareConjecture.Proofs.M30.Generalized.SpatialRegularity
import PoincareConjecture.Proofs.M30.Generalized.SpatialTopology
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction.SmoothInverse

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

theorem regularAt_of_slice_identity (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (ht : t = s)
    (f : (F.slice s).carrier → (F.slice t).carrier) (x : (F.slice s).carrier)
    (hf : ∀ᶠ y in 𝓝 x, (⟨t, f y⟩ : F.point) = (⟨s, y⟩ : F.point)) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x ∧
      Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f x) := by
  subst t
  have heq : f =ᶠ[𝓝 x] id := by
    filter_upwards [hf] with y hy
    exact eq_of_heq (Sigma.mk.inj_iff.mp hy).2
  refine ⟨contMDiffAt_id.congr_of_eventuallyEq heq, ?_⟩
  rw [heq.mfderiv_eq, mfderiv_id]
  exact Function.bijective_id

namespace Cylinder

theorem exists_of_singleton_family
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (hI : I.OrdConnected) (hIc : IsCompact I)
    (V : TopologicalSpace.Opens C.carrier) {U : Set C.carrier}
    (hU : IsOpen U) (hUn : U.Nonempty) (hUc : IsCompact (closure U))
    (hUV : closure U ⊆ V) (p : C.carrier → C.carrier)
    (e : ∀ x : C.carrier, GeneralizedFlowCylinder F C origin scale I {p x})
    {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    (hregular : ∀ x ∈ V,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => (e z).forward s₀ hs₀ (p z)) x ∧
        Function.Bijective
          (mfderiv (𝓡 3) (𝓡 3) (fun z => (e z).forward s₀ hs₀ (p z)) x))
    (hinitial : InjOn (fun z => (e z).forward s₀ hs₀ (p z)) V) :
    ∃ E : GeneralizedFlowCylinder F C origin scale I U,
      ∀ s (hs : s ∈ I) (x : C.carrier), E.pointMap s hs x = (e x).pointMap s hs (p x) := by
  classical
  let : Nonempty C.carrier := ⟨hUn.choose⟩
  let f := fun s (hs : s ∈ I) (x : C.carrier) => (e x).forward s hs (p x)
  have hreg (s : ℝ) (hs : s ∈ I) (x : C.carrier) (hx : x ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f s hs) x ∧
        Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (f s hs) x) :=
    regularAt_of_initial e hI x hs₀ (hregular x hx) s hs
  have hinj (s : ℝ) (hs : s ∈ I) : InjOn (f s hs) V := by
    intro x hx y hy hxy
    apply hinitial hx hy
    have hmeet : (e x).pointMap s hs (p x) = (e y).pointMap s hs (p y) :=
      congrArg (fun z => (⟨origin + s / scale, z⟩ : F.point)) hxy
    have hzero := pointMap_eq_on_interval (e x) (e y) hI (mem_singleton (p x))
      (mem_singleton (p y)) hs hmeet s₀ hs₀
    exact eq_of_heq (Sigma.mk.inj_iff.mp hzero).2
  have hUV' : U ⊆ V := subset_closure.trans hUV
  have hleft (s : ℝ) (hs : s ∈ I) :
      LeftInvOn (Function.invFunOn (f s hs) U) (f s hs) U :=
    ((hinj s hs).mono hUV').leftInvOn_invFunOn
  have hinverse (s : ℝ) (hs : s ∈ I) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Function.invFunOn (f s hs) U) (f s hs '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    have hlocal : ∀ᶠ z in 𝓝 x, Function.invFunOn (f s hs) U (f s hs z) = z := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact hleft s hs hz
    exact (Poincare.contMDiffAt_of_local_left_inverse (hreg s hs x (hUV' hx)).1
      (hreg s hs x (hUV' hx)).2 hlocal).contMDiffWithinAt
  let K : Set V := (Subtype.val : V → C.carrier) ⁻¹' closure U
  have hK : IsCompact K := Topology.IsInducing.subtypeVal.isCompact_preimage' hUc
    (fun x hx => ⟨⟨x, hUV hx⟩, rfl⟩)
  let inclusion : U → K := fun x => ⟨⟨x.1, hUV' x.2⟩, subset_closure x.2⟩
  have hinclusion : Topology.IsEmbedding inclusion := by
    have hcomp : Topology.IsEmbedding
        ((Subtype.val : V → C.carrier) ∘ (Subtype.val : K → V)) :=
      Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    apply hcomp.of_comp_iff.mp
    exact Topology.IsEmbedding.subtypeVal
  have hfV (s : ℝ) (hs : s ∈ I) : Continuous (fun x : V => f s hs x.1) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hreg s hs x.1 x.2).1.continuousAt.comp continuous_subtype_val.continuousAt
  have hinitialV : Function.Injective (fun x : V => (e x.1).forward s₀ hs₀ (p x.1)) := by
    intro x y hxy
    exact Subtype.ext (hinitial x.2 y.2 hxy)
  have hcompactEmbedding := isEmbedding_family_pointMap_on_compact
    (p := fun x : V => p x.1) (fun x : V => e x.1) hI hIc hfV hs₀ hinitialV hK
  have hembedding : Topology.IsEmbedding
      (fun z : I × U => (e z.2.1).pointMap z.1.1 z.1.2 (p z.2.1)) :=
    hcompactEmbedding.comp (Topology.IsEmbedding.id.prodMap hinclusion)
  let E : GeneralizedFlowCylinder F C origin scale I U := {
    scale_pos := (e hUn.choose).scale_pos
    forward := f
    inverse := fun s hs => Function.invFunOn (f s hs) U
    forward_smooth := fun s hs x hx => (hreg s hs x (hUV' hx)).1.contMDiffWithinAt
    inverse_smooth := hinverse
    left_inverse := hleft
    right_inverse := fun _ _ _ hx => Function.invFunOn_eq hx
    embedding := hembedding
    vertical_compatibility := fun s hs x _ =>
      (e x).vertical_compatibility s hs (p x) (mem_singleton (p x)) }
  exact ⟨E, fun _ _ _ => rfl⟩

end Cylinder

end PoincareConjecture.M30
