import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelPrimitive
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelPrimitive.Global.Sections
import PoincareConjecture.Proofs.Horizon.Topology.Sheaves.Continuation











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory Opposite Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ParallelPrimitive

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem primitive_germ_surjective
    (α : (x : M) → TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (U : Opens (TopCat.of M)) (f : M → ℝ)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hd : ∀ x ∈ U, mvfderiv (𝓡 n) f x = α x)
    (y : M) (hy : y ∈ U) : Function.Surjective ((primitivePresheaf α).germ U y hy) := by
  intro a
  obtain ⟨W, hyW, s, hs⟩ := (primitivePresheaf α).exists_germ_eq a
  let c : ℝ := s.val ⟨y, hyW⟩ - f y
  have hshift : ∀ x ∈ U, mvfderiv (𝓡 n) (fun z => f z + c) x = α x := by
    intro x hx
    rw [mvfderiv_fun_add
      ((hf.contMDiffAt (U.isOpen.mem_nhds hx)).mdifferentiableAt (by simp))
      mdifferentiableAt_const, mvfderiv_const, add_zero, hd x hx]
  let t : (primitivePresheaf α).obj (op U) :=
    ⟨fun x => f x + c, primitivePredicate_of_map α U (fun x => f x + c)
      (hf.add contMDiffOn_const) hshift⟩
  refine ⟨t, (primitive_germ_eq_of_value_eq α hy hyW t s ?_).trans hs⟩
  change f y + (s.val ⟨y, hyW⟩ - f y) = s.val ⟨y, hyW⟩
  ring



theorem locally_bijective_primitive_germ_of_parallel
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ (x : M) (u : TangentSpace (𝓡 n) x), D.connection V x u = 0)
    (x : M) :
    ∃ U : Opens (TopCat.of M), x ∈ U ∧ ∀ y (hy : y ∈ U),
      Function.Bijective ((primitivePresheaf (fun z => g.inner z (V z))).germ U y hy) := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨W, f, hW, hxW, hf, _, hd⟩ := D.exists_local_potential_of_parallel hV hparallel x 0
  let U : Opens (TopCat.of M) := ⟨connectedComponentIn W x, hW.connectedComponentIn⟩
  have hUsub : (U : Set M) ⊆ W := connectedComponentIn_subset W x
  refine ⟨U, mem_connectedComponentIn hxW, fun y hy => ⟨?_, ?_⟩⟩
  · exact primitive_germ_injective _ U isPreconnected_connectedComponentIn y hy
  · exact primitive_germ_surjective _ U f (hf.mono hUsub) (fun z hz => hd z (hUsub hz)) y hy

end PoincareConjecture.ParallelPrimitive

namespace PoincareConjecture.LeviCivitaData

open ParallelPrimitive



theorem exists_global_potential_of_parallel
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [SimplyConnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {V : (x : M) → TangentSpace (𝓡 n) x}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ (x : M) (u : TangentSpace (𝓡 n) x), D.connection V x u = 0)
    (p : M) (c : ℝ) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ f p = c ∧
      (∀ x, mvfderiv (𝓡 n) f x = g.inner x (V x)) ∧ D.gradient f = V := by
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  let α := fun x => g.inner x (V x)
  obtain ⟨W, f, hW, hpW, hf, hfp, hd⟩ := D.exists_local_potential_of_parallel hV hparallel p c
  let U : Opens (TopCat.of M) := ⟨W, hW⟩
  let s : (primitivePresheaf α).obj (op U) :=
    ⟨fun x => f x, primitivePredicate_of_map α U f hf hd⟩
  obtain ⟨t, hts⟩ := Poincare.Topology.exists_globalSection_of_locally_bijective_germ
    (primitivePredicate α) (locally_bijective_primitive_germ_of_parallel D hV hparallel)
    p ((primitivePresheaf α).germ U p hpW s)
  obtain ⟨ht, hdt⟩ := sectionExtension_spec α t.property
  refine ⟨sectionExtension ⊤ t.val, contMDiffOn_univ.mp ht, ?_,
    fun x => hdt x (by trivial), ?_⟩
  · obtain ⟨O, hpO, _, _, heq⟩ := (primitivePresheaf α).germ_eq p (by trivial) hpW t s hts
    have he := congrArg (fun a : (primitivePresheaf α).obj (op O) => a.val ⟨p, hpO⟩) heq
    rw [sectionExtension_apply ⊤ t.val (by trivial)]
    exact he.trans hfp
  · funext x
    rw [gradient, hdt x (by trivial)]
    exact (g.inner_isInvertible x).inverse_apply_self (V x)

end PoincareConjecture.LeviCivitaData
