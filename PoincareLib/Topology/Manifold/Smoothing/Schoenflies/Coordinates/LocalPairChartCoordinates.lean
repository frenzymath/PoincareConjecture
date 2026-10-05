import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Coordinates.ZeroSliceCharts

/-!
# Literal normal coordinates of the local pair chart

The inverse-chart formula retains the signed coordinate itself, in
addition to its zero set. See Brown derivations010 and013, section4.
-/

set_option autoImplicit false

open Set

namespace BrownCollar

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

/-- The actual pair chart fixes its complete base and has exactly
the original signed normal coordinate. Its entire target remains in
the supplied flattening domain. See Brown derivation013, section4. -/
theorem exists_local_pair_chart_with_normal
    (e : OpenPartialHomeomorph X (P × ℝ)) (S : Set X)
    (hpair : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : S) (hx : (x : X) ∈ e.source) :
    ∃ q : OpenPartialHomeomorph (S × ℝ) X,
      (x, (0 : ℝ)) ∈ q.source ∧ q.target ⊆ e.source ∧
      (∀ s, (s, (0 : ℝ)) ∈ q.source → q (s, 0) = (s : X)) ∧
      ∀ z ∈ q.source, (e (q z)).2 = z.2 := by
  obtain ⟨phi, hphiS, _, hformula⟩ := exists_zeroSliceChart e S hpair x hx
  let q := (phi.prod (OpenPartialHomeomorph.refl ℝ)).trans e.symm
  have hcoord (s : S) (hs : s ∈ phi.source) :
      (phi s, (0 : ℝ)) = e (s : X) := by
    apply Prod.ext
    · exact hformula s hs
    · have hsA : (s : X) ∈ e.source := by
        simpa only [hphiS, mem_preimage] using hs
      exact ((hpair _ hsA).mp s.property).symm
  have hxphi : x ∈ phi.source := by
    rw [hphiS]
    exact hx
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨hxphi, mem_univ _⟩, ?_⟩
    change (phi x, (0 : ℝ)) ∈ e.target
    rw [hcoord x hxphi]
    exact e.map_source hx
  · intro y hy
    exact hy.1
  · intro s hs
    change e.symm (phi s, (0 : ℝ)) = (s : X)
    rw [hcoord s hs.1.1]
    apply e.left_inv
    simpa only [hphiS, mem_preimage] using hs.1.1
  · intro z hz
    have hzE : (phi z.1, z.2) ∈ e.target := hz.2
    change (e (e.symm (phi z.1, z.2))).2 = z.2
    rw [e.right_inv hzE]

end BrownCollar
