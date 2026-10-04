import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.OriginalOppositeCollars
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.MatchedBoundaryProduct

/-!
# A whole small boundary product from the original domain

Construct both actual side collars and their literal finite PL
base comparison internally. The whole matched product retains its
original side equations and ambient-open strips. See055, section5
and Waldhausen1968 p.60.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
/-- The original compact domain and exterior construct one full
finite PL product about their entire common frontier. The source
contains no collar, base comparison or open-product supplier.
See Waldhausen1968 p.60 and rigidity055, section5. -/
theorem PLDomain.exists_small_boundary_product_of_interiors_nonempty
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hminus : IsCompact (interior R)ᶜ)
    (hne : (interior R).Nonempty) (hneminus : (interior (interior R)ᶜ).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (C : (s → ℝ × V3) × ℝ → X),
      L.faces.Finite ∧ PolyhedralPLInCharts e C (L.space ×ˢ Icc (-1 : ℝ) 1) ∧
      Topology.IsEmbedding
        (fun z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)) => C z) ∧
      (∀ x : L.space, C ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ Icc (-1 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)),
        (C z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
        (C z ∈ R ↔ 0 ≤ (z : (s → ℝ × V3) × ℝ).2) ∧
        (C z ∈ (interior R)ᶜ ↔ (z : (s → ℝ × V3) × ℝ).2 ≤ 0)) ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
        MapsTo C (L.space ×ˢ Icc (-delta) delta) U ∧
        ∀ eps : ℝ, 0 < eps → eps ≤ delta →
          IsOpen (C '' (L.space ×ˢ Ioo (-eps) eps)) := by
  have hboth := he.exists_opposite_small_boundary_collars hR hminus hne hneminus hU hBU
  obtain ⟨s, L, HB, c, hL, hc, hci, hcR, hc0, hcf,
    delta0, hdelta0, hdelta0b, hcU, hco⟩ := hboth R (Or.inl rfl)
  obtain ⟨t, K, HC, d, hK, hd, hdi, hdT, hd0, hdf,
    delta1, hdelta1, hdelta1b, hdU, hdo⟩ := hboth (interior R)ᶜ (Or.inr rfl)
  obtain ⟨C, hC⟩ := exists_matched_boundary_product he.cover he.compatible he.closed
    L hL K hK HB HC c d hc hd hci hdi hcR hdT hc0 hd0 hcf hdf
    delta0 delta1 hdelta0 hdelta1 hdelta0b hdelta1b hcU hdU hco hdo
  exact ⟨s, L, HB, C, hL, hC⟩

end PoincareMT.M76
