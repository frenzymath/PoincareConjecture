import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.Support
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Family








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs

private abbrev S1 := sphere (0 : E2) 1



theorem exists_planar_circle_family_extension
    {a b : Real} (hab : a ≤ b) (c : Real → S1 → E2)
    (hc : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × S1 => c z.1 z.2))
    (hemb : ∀ t ∈ Icc a b,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c t)) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        ∀ t ∈ Icc a b, ∀ q : S1, Φ t (c a q) = c t q := by
  have hinj (t : Real) (ht : t ∈ Icc a b) :
      Injective (fun z : Unit × S1 => c t z.2) := by
    intro x y h
    exact Prod.ext (Subsingleton.elim _ _) ((hemb t ht).isEmbedding.injective h)
  obtain ⟨Φ, hi, hs, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_circle_family hab
      (fun (_ : Unit) z => c z.1 z.2) (fun _ => hc) (fun _ => hemb) hinj
  exact ⟨K, hK, Φ, hi, hs, contDiff_family_symm Φ hs, hfix, hmotion ()⟩



theorem exists_planar_circle_pair_family_extension
    {a b : Real} (hab : a ≤ b) (c : Fin 2 → Real → S1 → E2)
    (hc : ∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × S1 => c i z.1 z.2))
    (hemb : ∀ i t, t ∈ Icc a b →
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i t))
    (hdisj : ∀ t ∈ Icc a b, Disjoint (range (c 0 t)) (range (c 1 t))) :
    ∃ K : Set E2, IsCompact K ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        ∀ i t, t ∈ Icc a b → ∀ q : S1, Φ t (c i a q) = c i t q := by
  have hinj (t : Real) (ht : t ∈ Icc a b) :
      Injective (fun z : Fin 2 × S1 => c z.1 t z.2) := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := by
      by_contra hn
      fin_cases i <;> fin_cases j
      · exact hn rfl
      · exact disjoint_left.mp (hdisj t ht) ⟨x, rfl⟩ ⟨y, h.symm⟩
      · exact disjoint_left.mp (hdisj t ht) ⟨y, h.symm⟩ ⟨x, rfl⟩
      · exact hn rfl
    subst j
    exact Prod.ext rfl ((hemb i t ht).isEmbedding.injective h)
  obtain ⟨Φ, hi, hs, ⟨K, hK, hfix⟩, hmotion⟩ :=
    exists_ambient_isotopy_of_circle_family hab
      (fun i z => c i z.1 z.2) hc hemb hinj
  exact ⟨K, hK, Φ, hi, hs, contDiff_family_symm Φ hs, hfix, hmotion⟩

end Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs
