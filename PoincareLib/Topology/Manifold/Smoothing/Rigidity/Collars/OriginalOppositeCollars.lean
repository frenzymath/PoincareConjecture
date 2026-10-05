import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.OriginalDomainBoundaryCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.CircleSlabInterior

/-!
# Both actual side collars with their common original boundary

The two finite parameter complexes remain distinct. Their boundary
homeomorphisms land in the same literal original frontier, using
the proved closed-exterior equality. See rigidity053, section5.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in
/-- The domain and its closed exterior each construct a full
small collar with the same physical boundary. No identification
of the two finite parameter spaces is asserted. See053, section5. -/
theorem PLDomain.exists_opposite_small_boundary_collars
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hminus : IsCompact (interior R)ᶜ)
    (hne : (interior R).Nonempty) (hneminus : (interior (interior R)ᶜ).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∀ Q ∈ ({R, (interior R)ᶜ} : Set (Set X)),
      ∃ (s : Finset Q) (L : SimplicialComplex ℝ (s → ℝ × V3))
        (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X),
        L.faces.Finite ∧ PolyhedralPLInCharts e c (L.space ×ˢ Icc (0 : ℝ) 1) ∧
        Topology.IsEmbedding
          (fun z : (L.space ×ˢ Icc (0 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
        MapsTo c (L.space ×ˢ Icc (0 : ℝ) 1) Q ∧
        (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
        (∀ z : (L.space ×ˢ Icc (0 : ℝ) 1 : Set ((s → ℝ × V3) × ℝ)),
          c z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 2 ∧
          MapsTo c (L.space ×ˢ Icc 0 delta) U ∧
          ∀ eps : ℝ, 0 < eps → eps ≤ delta →
            IsOpen ((Subtype.val : Q → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 eps))) := by
  intro Q hQ
  have hdata : IsCompact Q ∧ PLDomain e Q ∧
      frontier Q = frontier R ∧ (interior Q).Nonempty := by
    rcases hQ with hQ | hQ
    · rw [hQ]
      exact ⟨hR, he, rfl, hne⟩
    · rw [hQ]
      exact ⟨hminus, he.closed_exterior, he.frontier_closed_exterior, hneminus⟩
  obtain ⟨hcompact, heQ, hfront, hneQ⟩ := hdata
  have hQU : frontier Q ⊆ U := by rwa [hfront]
  obtain ⟨s, L, HB, c, hL, hcPL, hcemb, hcQ, hc0, hcfront,
    delta, hdelta, hdeltab, hthin, hopen⟩ :=
    heQ.exists_small_boundary_collar_of_interior_nonempty hcompact hneQ hU hQU
  let HB' := HB.trans (Homeomorph.setCongr hfront)
  refine ⟨s, L, HB', c, hL, hcPL, hcemb, hcQ, hc0, ?_,
    delta, hdelta, hdeltab, hthin, hopen⟩
  intro z
  rw [← hfront]
  exact hcfront z

end PoincareMT.M76
