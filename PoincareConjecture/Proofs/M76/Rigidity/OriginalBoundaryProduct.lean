import PoincareConjecture.Proofs.M76.Rigidity.OriginalOppositeCollars
import PoincareConjecture.Proofs.M76.Rigidity.MatchedBoundaryProduct










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in




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

end PoincareConjecture.M76
