import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Circle.Parametric
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.ParametricExtension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_ambient_isotopy_of_circle_isotopy
    {a b : Real} (hab : a ≤ b)
    (f : Real × sphere (0 : EuclideanSpace Real (Fin 2)) 1 ->
      EuclideanSpace Real (Fin 2))
    (hf : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ f)
    (hemb : ∀ t ∈ Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : sphere (0 : EuclideanSpace Real (Fin 2)) 1 => f (t, p))) :
    ∃ Phi : Real -> Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace Real (Fin 2)) (EuclideanSpace Real (Fin 2)) ∞,
      (∀ x, Phi a x = x) ∧
      ContDiff Real ∞ (fun z : Real × EuclideanSpace Real (Fin 2) => Phi z.1 z.2) ∧
      (∃ K : Set (EuclideanSpace Real (Fin 2)), IsCompact K ∧
        ∀ t x, x ∉ K -> Phi t x = x) ∧
      ∀ t ∈ Icc a b, ∀ p : sphere (0 : EuclideanSpace Real (Fin 2)) 1,
        Phi t (f (a, p)) = f (t, p) := by
  obtain ⟨G, hG, heq⟩ := exists_contDiff_extension_sphere_family
    (T := Icc a b) isCompact_Icc f hf
  have hembG : ∀ t ∈ Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : S1 => G (t, p)) := by
    intro t ht
    simpa only [funext (heq t ht)] using hemb t ht
  obtain ⟨e, he, _, _, hei, _, hagree⟩ :=
    exists_parametric_circle_neighborhood isCompact_Icc G hG hembG
  obtain ⟨Phi, hi, hs, hfix, hmotion⟩ :=
    exists_ambient_isotopy_of_compact_isotopy (isCompact_sphere 0 1) G hG e he hei
      (fun t ht x hx => hagree t ht ⟨x, hx⟩)
  refine ⟨Phi, hi, hs, hfix, fun t ht p => ?_⟩
  simpa only [heq a ⟨le_rfl, hab⟩ p, heq t ht p] using hmotion t ht p p.property

end Poincare.Manifold.Schoenflies
