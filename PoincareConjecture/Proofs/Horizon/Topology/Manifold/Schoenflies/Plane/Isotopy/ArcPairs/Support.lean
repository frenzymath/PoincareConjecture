import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeLocal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs

abbrev E2 := EuclideanSpace Real (Fin 2)

open SaddleLevel

theorem contDiff_family_symm
    (Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2)) :
    ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) := by
  have hm : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Φ z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hΦ.contMDiff
  have hi := Poincare.Manifold.contMDiff_diffeomorph_family_symm Φ hm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hi
  exact hi.contDiff



theorem eventuallyEq_of_supported_matching
    {α β : Real → E2} {A K : Set E2} {J : Set Real} {s : Real}
    (hK : IsCompact K) (hKA : Disjoint K A)
    (hα : ContinuousWithinAt α J s) (hs : α s ∈ A)
    (D : E2 → E2) (hfix : ∀ x, x ∉ K → D x = x)
    (hmatch : ∀ t ∈ J, D (α t) = β t) :
    α =ᶠ[𝓝[J] s] β := by
  have hsK : α s ∈ Kᶜ := fun hx => disjoint_left.mp hKA hx hs
  have hnear : ∀ᶠ t in 𝓝[J] s, α t ∈ Kᶜ :=
    hα (hK.isClosed.isOpen_compl.mem_nhds hsK)
  filter_upwards [hnear, self_mem_nhdsWithin] with t ht htJ
  exact (hfix (α t) ht).symm.trans (hmatch t htJ)




theorem exists_planar_arc_isotopy_rel_square_and_arc_of_interval_isotopy
    {ρ a b l l₀ l₁ u₁ u₀ u : Real} (hab : a < b)
    (hll₀ : l ≤ l₀) (hl₀l₁ : l₀ < l₁) (hl₁u₁ : l₁ ≤ u₁)
    (hu₁u₀ : u₁ < u₀) (hu₀u : u₀ ≤ u)
    {A : Set E2} (hA : IsCompact A)
    (F : Real × Real → E2) {W : Set (Real × Real)}
    (hW : IsOpen W) (hrect : Icc a b ×ˢ Icc l u ⊆ W)
    (hF : ContDiffOn Real ∞ F W)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun s => F (t, s)) (Icc l u))
    (hder : ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, deriv (fun y => F (t, y)) s ≠ 0)
    (hstationary : ∀ t ∈ Icc a b, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
      F (t, s) = F (a, s))
    (htrace : ∀ t ∈ Icc a b, ∀ s ∈ Icc l₁ u₁,
      F (t, s) ∉ closedSquare ρ ∪ A) :
    ∃ K : Set E2, IsCompact K ∧ Disjoint K (closedSquare ρ ∪ A) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ a x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        (∀ t x, x ∈ closedSquare ρ ∪ A → Φ t x = x) ∧
        ∀ t ∈ Icc a b, ∀ s ∈ Icc l u, Φ t (F (a, s)) = F (t, s) := by
  have hU : IsOpen (closedSquare ρ ∪ A)ᶜ :=
    ((isClosed_closedSquare ρ).union hA.isClosed).isOpen_compl
  obtain ⟨K, O, hK, hKU, hO, hendO, hKO, Φ, hi, hΦ, hfix, hfixO, hm⟩ :=
    exists_relative_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
      hab hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u hU F hW hrect hF hinj hder
      hstationary htrace
  have hdisj : Disjoint K (closedSquare ρ ∪ A) :=
    disjoint_left.mpr (fun _ hx hy => hKU hx hy)
  exact ⟨K, hK, hdisj, Φ, hi, hΦ, contDiff_family_symm Φ hΦ, hfix,
    fun t x hx => hfix t x (fun hxK => disjoint_left.mp hdisj hxK hx), hm⟩

end Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs
