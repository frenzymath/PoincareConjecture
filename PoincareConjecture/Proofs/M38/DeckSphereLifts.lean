import PoincareConjecture.Proofs.M38.SmoothSphereLift
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_equivariant_sphere_lifts
    {G : Type*} [Group G] [MulAction G UnitThreeSphere]
    (q : UnitThreeSphere → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hsurj : Function.Surjective q)
    (e : G → Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞)
    (he : ∀ (g : G) (x : UnitThreeSphere), e g x = g • x)
    (hdeck : ∀ (g : G) (x : UnitThreeSphere), q (g • x) = q x)
    (hfree : ∀ (g : G) (x : UnitThreeSphere), g • x = x → g = 1)
    (hfibers : ∀ (x y : UnitThreeSphere), q x = q y → ∃ g : G, y = g • x)
    (f : UnitTwoSphere → M) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ F : G → UnitTwoSphere → UnitThreeSphere,
      (∀ g, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F g)) ∧
      (∀ g z, q (F g z) = f z) ∧
      (∀ g h z, F (g * h) z = g • F h z) ∧
      (∀ g h, g ≠ h → Disjoint (range (F g)) (range (F h))) ∧
      q ⁻¹' range f = ⋃ g, range (F g) := by
  let z₀ : UnitTwoSphere := Poincare.Topology.standardSpherePole 0
  obtain ⟨p₀, hp₀⟩ := hsurj (f z₀)
  have hcover : IsCoveringMap q :=
    isLocalHomeomorph_iff_isCoveringMap.mp hq.isLocalHomeomorph
  obtain ⟨L, hL, _, hqL⟩ := exists_smooth_sphere_lift q hq hcover f hf z₀ p₀ hp₀
  let F : G → UnitTwoSphere → UnitThreeSphere := fun g z => e g (L z)
  have hF (g : G) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F g) :=
    hL.comp_localDiffeomorph (e g).isLocalDiffeomorph
      ((e g).injective.comp hL.isEmbedding.injective)
  have hqF (g : G) (z : UnitTwoSphere) : q (F g z) = f z := by
    change q (e g (L z)) = f z
    rw [he, hdeck, hqL]
  refine ⟨F, hF, hqF, ?_, ?_, ?_⟩
  · intro g h z
    change e (g * h) (L z) = g • e h (L z)
    rw [he, he, mul_smul]
  · intro g h hgh
    apply disjoint_left.mpr
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hab : a = b := hf.isEmbedding.injective
      ((hqF g a).symm.trans ((congrArg q (ha.trans hb.symm)).trans (hqF h b)))
    subst b
    have heq : g • L a = h • L a := by
      simpa only [F, he] using ha.trans hb.symm
    have hfix : (h⁻¹ * g) • L a = L a := by
      rw [mul_smul, heq, inv_smul_smul]
    have hunit := hfree (h⁻¹ * g) (L a) hfix
    exact hgh (by simpa using congrArg (h * ·) hunit)
  · ext x
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨g, hg⟩ := hfibers (L z) x ((hqL z).trans hz)
      exact mem_iUnion.mpr ⟨g, z, by simpa only [F, he] using hg.symm⟩
    · intro hx
      obtain ⟨g, z, rfl⟩ := mem_iUnion.mp hx
      exact ⟨z, (hqF g z).symm⟩

end PoincareConjecture.M38
