import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelPrimitive.Global.Uniqueness
import Mathlib.Topology.Sheaves.LocalPredicate



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ParallelPrimitive

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def primitivePrelocal (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
    TopCat.PrelocalPredicate (fun _ : TopCat.of M => ℝ) where
  pred {U} f := ∃ k : M → ℝ, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ k U ∧
    (∀ x ∈ U, mvfderiv (𝓡 n) k x = α x) ∧ ∀ x : U, k x = f x
  res {U V} i f hf := by
    obtain ⟨k, hk, hd, heq⟩ := hf
    exact ⟨k, hk.mono i.le, fun x hx => hd x (i.le hx),
      fun x => heq ⟨x, i.le x.property⟩⟩


def primitivePredicate (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ) :
    TopCat.LocalPredicate (fun _ : TopCat.of M => ℝ) :=
  (primitivePrelocal α).sheafify

abbrev primitivePresheaf (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
  (TopCat.subsheafToTypes (primitivePredicate α)).presheaf


def sectionExtension (U : Opens (TopCat.of M)) (f : U → ℝ) : M → ℝ := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

theorem sectionExtension_apply (U : Opens (TopCat.of M)) (f : U → ℝ)
    {x : M} (hx : x ∈ U) : sectionExtension U f x = f ⟨x, hx⟩ := by
  simp [sectionExtension, hx]

omit [IsManifold (𝓡 n) ∞ M] in
theorem sectionExtension_spec
    (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    {U : Opens (TopCat.of M)} {f : U → ℝ} (hf : (primitivePredicate α).pred f) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (sectionExtension U f) U ∧
      ∀ x ∈ U, mvfderiv (𝓡 n) (sectionExtension U f) x = α x := by
  have hlocal (x : M) (hx : x ∈ U) :
      ∃ k : M → ℝ, sectionExtension U f =ᶠ[𝓝 x] k ∧
        ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ k x ∧ mvfderiv (𝓡 n) k x = α x := by
    obtain ⟨V, hxV, i, k, hk, hd, heq⟩ := hf ⟨x, hx⟩
    refine ⟨k, ?_, hk.contMDiffAt (V.isOpen.mem_nhds hxV), hd x hxV⟩
    filter_upwards [V.isOpen.mem_nhds hxV] with y hy
    rw [sectionExtension_apply U f (i.le hy)]
    exact (heq ⟨y, hy⟩).symm
  constructor
  · intro x hx
    obtain ⟨k, heq, hk, _⟩ := hlocal x hx
    exact (hk.congr_of_eventuallyEq heq).contMDiffWithinAt
  · intro x hx
    obtain ⟨k, heq, _, hd⟩ := hlocal x hx
    calc
      mvfderiv (𝓡 n) (sectionExtension U f) x = mvfderiv (𝓡 n) k x := by
        unfold mvfderiv
        rw [heq.mfderiv_eq, heq.eq_of_nhds]
      _ = α x := hd

omit [IsManifold (𝓡 n) ∞ M] in
theorem primitivePredicate_of_map
    (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (U : Opens (TopCat.of M)) (f : M → ℝ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hd : ∀ x ∈ U, mvfderiv (𝓡 n) f x = α x) :
    (primitivePredicate α).pred (fun x : U => f x) :=
  TopCat.PrelocalPredicate.sheafifyOf ⟨f, hf, hd, fun _ => rfl⟩


theorem primitive_germ_eq_of_value_eq
    (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    {U V : Opens (TopCat.of M)} {x : M} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : (primitivePresheaf α).obj (op U)) (t : (primitivePresheaf α).obj (op V))
    (heq : s.val ⟨x, hxU⟩ = t.val ⟨x, hxV⟩) :
    (primitivePresheaf α).germ U x hxU s = (primitivePresheaf α).germ V x hxV t := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let W : Opens (TopCat.of M) :=
    ⟨connectedComponentIn ((U : Set M) ∩ V) x, (U.isOpen.inter V.isOpen).connectedComponentIn⟩
  have hWsub : (W : Set M) ⊆ (U : Set M) ∩ V := connectedComponentIn_subset _ _
  have hxW : x ∈ W := mem_connectedComponentIn ⟨hxU, hxV⟩
  let iU : W ⟶ U := homOfLE (fun _ hy => (hWsub hy).1)
  let iV : W ⟶ V := homOfLE (fun _ hy => (hWsub hy).2)
  obtain ⟨hs, hds⟩ := sectionExtension_spec α s.property
  obtain ⟨ht, hdt⟩ := sectionExtension_spec α t.property
  have h := eqOn_of_mvfderiv_eq W isPreconnected_connectedComponentIn
    (hs.mono iU.le) (ht.mono iV.le)
    (fun y hy => (hds y (iU.le hy)).trans (hdt y (iV.le hy)).symm) hxW
    (by simpa only [sectionExtension_apply U s.val hxU, sectionExtension_apply V t.val hxV]
      using heq)
  apply (primitivePresheaf α).germ_ext W hxW iU iV
  apply Subtype.ext
  funext y
  change s.val ⟨y, iU.le y.property⟩ = t.val ⟨y, iV.le y.property⟩
  simpa only [sectionExtension_apply U s.val (iU.le y.property),
    sectionExtension_apply V t.val (iV.le y.property)] using h y.property


theorem primitive_germ_injective
    (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (U : Opens (TopCat.of M)) (hUc : IsPreconnected (U : Set M))
    (x : M) (hx : x ∈ U) : Function.Injective ((primitivePresheaf α).germ U x hx) := by
  intro s t hst
  have he : s.val ⟨x, hx⟩ = t.val ⟨x, hx⟩ := by
    obtain ⟨W, hxW, _, _, hres⟩ := (primitivePresheaf α).germ_eq x hx hx s t hst
    exact congrArg (fun a : (primitivePresheaf α).obj (op W) => a.val ⟨x, hxW⟩) hres
  obtain ⟨hs, hds⟩ := sectionExtension_spec α s.property
  obtain ⟨ht, hdt⟩ := sectionExtension_spec α t.property
  have h := eqOn_of_mvfderiv_eq U hUc hs ht
    (fun y hy => (hds y hy).trans (hdt y hy).symm) hx
    (by simpa only [sectionExtension_apply U s.val hx, sectionExtension_apply U t.val hx]
      using he)
  apply Subtype.ext
  funext y
  simpa only [sectionExtension_apply U s.val y.property,
    sectionExtension_apply U t.val y.property] using h y.property

end PoincareConjecture.ParallelPrimitive
