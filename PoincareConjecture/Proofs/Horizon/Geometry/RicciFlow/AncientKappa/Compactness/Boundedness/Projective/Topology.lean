import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Projective
import Mathlib.Topology.Homeomorph.Lemmas









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture



theorem exists_projectiveCentralSection_homeomorph
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (f : UnitTwoSphere → M) (hf : Continuous f)
    (hfiber : ∀ x y, f x = f y ↔ y = x ∨ y = -x) :
    ∃ e : RealProjectiveTwo ≃ₜ Set.range f,
      ∀ x : UnitTwoSphere, (e (Quotient.mk realProjectiveTwoSetoid x)).val = f x := by
  have hrespect : ∀ x y, realProjectiveTwoSetoid x y →
      (⟨f x, mem_range_self x⟩ : Set.range f) = ⟨f y, mem_range_self y⟩ := by
    intro x y hxy
    apply Subtype.ext
    apply (hfiber x y).mpr
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.symm
    · right
      rw [hxy]
      simp
  let F : RealProjectiveTwo → Set.range f :=
    Quotient.lift (fun x => (⟨f x, mem_range_self x⟩ : Set.range f)) hrespect
  have hF : Continuous F := (hf.subtype_mk fun x => mem_range_self x).quotient_lift hrespect
  have hbij : Function.Bijective F := by
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h x =>
        induction b using Quotient.inductionOn with | h y =>
          apply Quotient.sound
          have hxy : f x = f y := congrArg Subtype.val hab
          rcases (hfiber x y).mp hxy with hxy | hxy
          · exact Or.inl hxy.symm
          · right
            rw [hxy]
            simp
    · rintro ⟨y, x, rfl⟩
      exact ⟨Quotient.mk realProjectiveTwoSetoid x, rfl⟩
  let e := (Equiv.ofBijective F hbij).toHomeomorphOfContinuousClosed hF hF.isClosedMap
  exact ⟨e, fun x => rfl⟩

namespace AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space



theorem eventually_projectiveCentralSection_homeomorph
    {C : ℕ → FlowCarrier.{0} 3} {g : ∀ k, ℝ → (C k).metric}
    {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T)
    (Φ : RoundCylinderSpace → G.limitCarrier.carrier)
    (hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (hfiber : ∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) :
    ∀ᶠ i in atTop,
      ∃ e : RealProjectiveTwo ≃ₜ Set.range (fun x : UnitTwoSphere => G.embedding i (Φ (x, 0))),
        ∀ x : UnitTwoSphere,
          (e (Quotient.mk realProjectiveTwoSetoid x)).val = G.embedding i (Φ (x, 0)) := by
  filter_upwards [G.eventually_cylinderCover_slab_regular Φ hΦ (-1) 1,
    G.eventually_cylinderCover_antipodal_fibers Φ hΦ.contMDiff.continuous hfiber (-1) 1]
    with i hlocal hfibers
  let f : UnitTwoSphere → (C (G.subsequence i)).carrier :=
    fun x => G.embedding i (Φ (x, 0))
  have hzero (x : UnitTwoSphere) : (x, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 :=
    ⟨mem_univ _, by norm_num⟩
  have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f := by
    intro x
    have he : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (G.embedding i ∘ Φ) (x, 0) :=
      (hlocal ⟨(x, 0), hzero x⟩).contMDiffAt
    have hpair : ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun y : UnitTwoSphere => (y, (0 : ℝ))) x :=
      contMDiffAt_id.prodMk contMDiffAt_const
    change ContMDiffAt (𝓡 2) (𝓡 3) ∞
      ((G.embedding i ∘ Φ) ∘ fun y : UnitTwoSphere => (y, (0 : ℝ))) x
    exact he.comp x hpair
  apply exists_projectiveCentralSection_homeomorph f hf.continuous
  intro x y
  have h := hfibers (x, 0) ⟨mem_univ _, by norm_num⟩
    (y, 0) ⟨mem_univ _, by norm_num⟩
  simpa only [Prod.mk.injEq, and_true] using h

end AncientPointedGeometricConvergence

end PoincareConjecture
