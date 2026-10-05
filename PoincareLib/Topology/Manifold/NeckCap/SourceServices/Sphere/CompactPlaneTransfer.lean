import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Sphere.CompactChartTransport
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Sphere.StereographicReduction

/-!
# Transfer of the actual compact planar isotopy to the sphere

Smale, Theorem 5, pp. 624-625, and corrected L3 Step 1e. One compact
support for all real times gives a genuine identity neighborhood at
the omitted pole. See
`smale/derivations/2026-09-22-sphere-reduction-compact-transfer.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M25.Topology3D

/-- The exact compact planar isotopy input, with actual inverses and
one support for all real times; Munkres, Theorem 1.3, pp. 193-194,
in the form consumed by Smale's pole reduction, Theorem 5, p. 625. -/
def CompactPlanarIsotopyProperty : Prop :=
  ∀ (h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)) {K : Set (ℝ × ℝ)}, IsCompact K →
    (∀ x, x ∉ K → h x = x) →
    ∃ H : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (H p.1).symm p.2) ∧
      (∀ t, t ≤ 0 → ∀ x, H t x = h x) ∧
      (∀ t, 1 ≤ t → ∀ x, H t x = x) ∧
      ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ t x, x ∉ Q → H t x = x ∧ (H t).symm x = x

/-- The actual compact plane isotopy gives an actual jointly smooth
sphere isotopy for a map fixed near the pole; Smale, Theorem 5,
pp. 624-625, and corrected L3 Step 1e. -/
theorem exists_sphere_isotopy_of_identity_near_pole
    (hPlane : CompactPlanarIsotopyProperty) (p : UnitTwoSphere)
    (g : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {U : Set UnitTwoSphere} (hU : IsOpen U) (hp : p ∈ U)
    (hfix : ∀ x ∈ U, g x = x) :
    ∃ J : ℝ → UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × UnitTwoSphere => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × UnitTwoSphere => (J q.1).symm q.2) ∧
      (∀ t, t ≤ 0 → ∀ x, J t x = g x) ∧
      (∀ t, 1 ≤ t → ∀ x, J t x = x) := by
  obtain ⟨h, K, hK, _, _, hhfix, hrecover⟩ :=
    exists_compact_planar_representative p g hU hp hfix
  obtain ⟨H, hH, hHI, hH0, hH1, Q, hQ, hHfix⟩ :=
    hPlane h hK (fun x hx => (hhfix x hx).1)
  let T := spherePlaneChart p
  have ht : T.target = univ := spherePlaneChart_target p
  obtain ⟨J, hJ, _, hJs, hJi, _, hJfix⟩ :=
    exists_compact_chart_diffeomorph_family (𝓡 2) T ht
      (contMDiffOn_spherePlaneChart p) (contMDiff_spherePlaneChart_symm p)
      H hH hHI hQ (fun t x hx => (hHfix t x hx).1)
  have hnot : p ∉ T.symm '' Q := by
    rintro ⟨y, _, heq⟩
    have hs : T.symm y ∈ T.source := T.map_target (ht ▸ mem_univ y)
    rw [heq] at hs
    simp only [T, spherePlaneChart_source, mem_compl_iff, mem_singleton_iff,
      not_true_eq_false] at hs
  refine ⟨J, hJs, hJi, ?_, ?_⟩
  · intro t ht0 x
    by_cases hx : x = p
    · subst x
      exact (hJfix t p hnot).1.trans (hfix p hp).symm
    · have hxs : x ∈ T.source := by
        simpa only [T, spherePlaneChart_source, mem_compl_iff, mem_singleton_iff] using hx
      rw [hJ t x hxs, hH0 t ht0]
      exact hrecover x hx
  · intro t ht1 x
    by_cases hx : x = p
    · subst x
      exact (hJfix t p hnot).1
    · have hxs : x ∈ T.source := by
        simpa only [T, spherePlaneChart_source, mem_compl_iff, mem_singleton_iff] using hx
      rw [hJ t x hxs, hH1 t ht1, T.left_inv hxs]

end PoincareMT.M25.Topology3D
