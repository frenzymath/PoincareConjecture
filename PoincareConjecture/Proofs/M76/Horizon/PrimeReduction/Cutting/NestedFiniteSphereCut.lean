import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NestedCollarCut
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLHalfspaceNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteSphereBicollars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarFrontier

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1

theorem PLDomain.exists_compact_ambient_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) :
    ∃ P : Set X, IsCompact P ∧ R ⊆ interior P ∧ PLDomain e P := by
  let := ChartedSpace.ofChartCover e he.cover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace V3 X
  obtain ⟨P, hP, hRP, _, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible
      he.cover hR isOpen_univ (subset_univ _)
  exact ⟨P, hP, hRP, he.cover, he.compatible, hP.isClosed, hhalf⟩

theorem finite_collar_removed_set_geometry
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R P V : Set X}
    (t : κ → Finset P)
    (N : ∀ i, SimplicialComplex ℝ (t i → ℝ × V3))
    (c : ∀ i, (t i → ℝ × V3) × ℝ → X) (δ : κ → ℝ)
    (hN : ∀ i, (N i).faces.Finite)
    (hc : ∀ i, PolyhedralPLInCharts e (c i) ((N i).space ×ˢ J))
    (hδ : ∀ i, 0 < δ i ∧ δ i ≤ 1 / 2)
    (hinside : ∀ i, MapsTo (c i) ((N i).space ×ˢ Icc (-δ i) (δ i))
      (V ∩ interior R))
    (hRP : R ⊆ interior P)
    (hQ : IsClosed (P \ ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2)))) :
    let O := ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
    IsOpen O ∧ closure O ⊆ V ∩ interior R ∧
      ∀ b : κ × Bool,
        c b.1 '' ((N b.1).space ×ˢ
          ({if b.2 then δ b.1 / 2 else -(δ b.1 / 2)} : Set ℝ)) ⊆ closure O := by
  let O := ⋃ i, c i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  let D := ⋃ i, c i '' ((N i).space ×ˢ Icc (-δ i) (δ i))
  have hOD : O ⊆ D := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨i, z, ⟨hz.1, ?_⟩, rfl⟩
    constructor <;> linarith [(hδ i).1, hz.2.1, hz.2.2]
  have hDR : D ⊆ V ∩ interior R := by
    intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    exact hinside i hz
  have hDc : IsCompact D := by
    apply isCompact_iUnion
    intro i
    apply ((N i).isCompact_space_of_finite (hN i)).prod isCompact_Icc |>.image_of_continuousOn
    apply (hc i).continuousOn.mono
    intro z hz
    refine ⟨hz.1, ?_⟩
    constructor <;> linarith [(hδ i).2, hz.2.1, hz.2.2]
  have hOP : O ⊆ interior P :=
    hOD.trans hDR |>.trans inter_subset_right |>.trans interior_subset |>.trans hRP
  have hOeq : O = interior P \ (P \ O) := by
    ext x
    constructor
    · exact fun hx => ⟨hOP hx, fun hn => hn.2 hx⟩
    · intro hx
      by_contra hn
      exact hx.2 ⟨interior_subset hx.1, hn⟩
  refine ⟨?_, (closure_minimal hOD hDc.isClosed).trans hDR, ?_⟩
  · change IsOpen O
    rw [hOeq]
    exact isOpen_interior.sdiff hQ
  · intro b
    have hcl := (hc b.1).continuousOn.closure_image_collar_strip
      ((N b.1).isCompact_space_of_finite (hN b.1))
      (by linarith [(hδ b.1).1] : 0 < δ b.1 / 2)
      (by linarith [(hδ b.1).2] : δ b.1 / 2 ≤ 1)
    apply subset_trans _ (closure_mono (subset_iUnion _ b.1))
    rw [hcl]
    apply image_mono
    rintro z ⟨hzN, hzt⟩
    refine ⟨hzN, ?_⟩
    change z.2 = (if b.2 then δ b.1 / 2 else -(δ b.1 / 2)) at hzt
    rw [hzt]
    split_ifs <;> constructor <;> linarith [(hδ b.1).1]

end PoincareConjecture.M76
