import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.ContinuousFiberInterpolation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointMidpointFibers
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.TwistedInvolutionInterval

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem prismFiberEndPair_interpolation {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (t : I) :
    prismFiberEndPair H (prismFiberInterpolation H x t) = prismFiberEndPair H x := by
  simp only [prismFiberEndPair,prismFiberInterpolation,prismFiberPoint,H.symm_apply_apply]

theorem prismFiberInterpolation_endpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (a : A) (b : Bool) (t : I) :
    prismFiberInterpolation H (prismEndMap H a b) t =
      H ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩ := by
  apply H.symm.injective
  simp only [prismFiberInterpolation,prismFiberPoint,prismEndMap,H.symm_apply_apply]
  apply Subtype.ext
  cases b <;> simp [fiberInterpolation,fiberFlip,unitInterval.symm]

def prismEndpointFiberMap {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i))) :
    C((⋃ i, prismEnds (H i)) × I, (⋃ i, B i)) :=
  ⟨fun z => L (prismEndpointInclusion H z.1,z.2),
    L.continuous.comp (((continuous_prismEndpointInclusion H).comp continuous_fst).prodMk continuous_snd)⟩

theorem prismEndpointFiberMap_apply
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (i : ι) (a : A i) (b : Bool) (t : I) :
    (prismEndpointFiberMap H L (prismEndpointLift H i a b,t) : E) =
      H i ⟨(a,fiberFlip b t),a.property,(fiberFlip b t).property⟩ :=
  (hL i (prismEndMap (H i) a b) t).trans
    (congrArg Subtype.val (prismFiberInterpolation_endpoint (H i) a b t))

theorem prismEndpointFiberMap_fiber_injective
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (p : (⋃ i, prismEnds (H i) : Set E)) :
    Function.Injective (fun t => prismEndpointFiberMap H L (p,t)) := by
  obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
  have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
  rw [hp']
  intro t s hts
  have he := congrArg (fun z : (⋃ i, B i : Set E) => (z : E)) hts
  rw [prismEndpointFiberMap_apply H L hL,prismEndpointFiberMap_apply H L hL] at he
  have hi := (H i).injective (Subtype.ext he)
  exact (fiberFlip b).injective (Subtype.ext (congrArg (fun z : (A i ×ˢ I : Set (E × ℝ)) =>
    (z : E × ℝ).2) hi))

theorem prismEndpointFiberMap_surjective
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t) : Function.Surjective (prismEndpointFiberMap H L) := by
  intro x
  obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
  let y := (H i).symm ⟨x,hi⟩
  let a : A i := ⟨(y : E × ℝ).1,y.property.1⟩
  let t : I := ⟨(y : E × ℝ).2,y.property.2⟩
  refine ⟨(prismEndpointLift H i a false,t),?_⟩
  apply Subtype.ext
  exact (prismEndpointFiberMap_apply H L hL i a false t).trans
    (congrArg Subtype.val ((H i).apply_symm_apply ⟨x,hi⟩))

theorem prismEndpointFiberMap_flip
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i)))
    (hτends : ∀ i (x : A i) (b : Bool),
      (τ (prismEndpointLift H i x b) : E) = prismEndMap (H i) x (!b))
    (p : (⋃ i, prismEnds (H i) : Set E)) (t : I) :
    prismEndpointFiberMap H L (τ p,t) = prismEndpointFiberMap H L (p,unitInterval.symm t) := by
  obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
  have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
  have hτp : τ (prismEndpointLift H i a b) = prismEndpointLift H i a (!b) := Subtype.ext (hτends i a b)
  rw [hp',hτp]
  apply Subtype.ext
  rw [prismEndpointFiberMap_apply H L hL,prismEndpointFiberMap_apply H L hL]
  have hb : fiberFlip (!b) t = fiberFlip b (unitInterval.symm t) := by
    cases b <;> simp
  rw [hb]

end PoincareConjecture.M76.PrismBelt
