import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineHypersurfaceCharts

/-!
# Properness puts every free interior-phase point inside the half-carrier

The retained whole active face lies inside the full support box.
Its points on the zero plane are exactly original rim points, all
already in the fixed prefix. Every remaining point has strictly
positive affine height and lies inside the actual closed half-box.
See Hudson1969, Lemma4.6, and Dehn032, section6.
-/

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

/-- The original whole-boundary properness equation and complete
rim inclusion discharge the free-face interior condition for the
actual half-carrier. No pointwise interior supplier is assumed for
the half-carrier itself. See Dehn032, section6. -/
theorem free_source_inside_half_carrier
    {U X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : OpenPartialHomeomorph X E) (ell : E →ᴬ[ℝ] ℝ)
    {D A P S : Set U} {R : Set X} {J C : Set E} {f : U → X}
    (hC : C = J ∩ {z | 0 ≤ ell z})
    (hSD : S ⊆ D) (hAP : A ⊆ P) (hfR : MapsTo f D R)
    (hproper : ∀ x ∈ D, f x ∈ frontier R ↔ x ∈ A)
    (hfQ : MapsTo f S Q.source)
    (hhalf : ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y))
    (hfront : ∀ y ∈ Q.source, y ∈ frontier R ↔ ell (Q y) = 0)
    (hfull : ∀ x ∈ S, Q (f x) ∈ interior J) :
    ∀ x ∈ S, x ∉ P → Q (f x) ∈ interior C := by
  intro x hx hxP
  have hnonneg : 0 ≤ ell (Q (f x)) := (hhalf _ (hfQ hx)).mp (hfR (hSD hx))
  have hne : ell (Q (f x)) ≠ 0 := by
    intro hz
    exact hxP (hAP ((hproper x (hSD hx)).mp ((hfront _ (hfQ hx)).mpr hz)))
  have hpos : 0 < ell (Q (f x)) := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hstrict : {z | 0 < ell z} ⊆ {z | 0 ≤ ell z} :=
    fun z hz => (show 0 < ell z from hz).le
  have hheight : Q (f x) ∈ interior {z | 0 ≤ ell z} :=
    interior_maximal hstrict (isOpen_lt continuous_const ell.continuous) hpos
  rw [hC, interior_inter]
  exact ⟨hfull x hx, hheight⟩

end OpenPartialHomeomorph
