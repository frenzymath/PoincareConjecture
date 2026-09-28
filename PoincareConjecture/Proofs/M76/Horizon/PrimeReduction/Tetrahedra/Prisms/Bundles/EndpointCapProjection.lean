import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointFiniteTopology
import Mathlib.Data.Set.Card

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem finite_fiber_of_prism_cell_maps
    {E ι : Type*} [TopologicalSpace E] [Zero E] [Finite ι]
    {A B D : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (C : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ D i)
    (r : E → E) (hr : ∀ i x, r (C i x) = H i x) (y : E) :
    ((⋃ i, D i) ∩ r ⁻¹' {y}).Finite ∧
      ((⋃ i, D i) ∩ r ⁻¹' {y}).ncard ≤ Nat.card ι := by
  classical
  let q : ι → E := fun i => if hy : y ∈ B i then C i ((H i).symm ⟨y,hy⟩) else 0
  have hsub : ((⋃ i, D i) ∩ r ⁻¹' {y}) ⊆ range q := by
    rintro x ⟨hx,hxy⟩
    change r x = y at hxy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    let z := (C i).symm ⟨x,hi⟩
    have he : (H i z : E) = y := by
      rw [← hr]
      change r (C i ((C i).symm ⟨x,hi⟩)) = y
      simpa only [(C i).apply_symm_apply] using hxy
    have hy : y ∈ B i := he ▸ (H i z).property
    have hz : z = (H i).symm ⟨y,hy⟩ := by
      apply (H i).injective
      rw [(H i).apply_symm_apply]
      exact Subtype.ext he
    refine ⟨i,?_⟩
    dsimp only [q]
    rw [dif_pos hy,← hz]
    exact congrArg Subtype.val ((C i).apply_symm_apply ⟨x,hi⟩)
  refine ⟨(finite_range q).subset hsub,(ncard_le_ncard hsub (finite_range q)).trans ?_⟩
  rw [← image_univ]
  exact (ncard_image_le (finite_univ : (univ : Set ι).Finite)).trans (by rw [ncard_univ])

theorem image_prism_ends_of_cell_maps
    {E ι : Type*} [TopologicalSpace E] {A B D : ι → Set E}
    (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (C : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ D i)
    (r : E → E) (hr : ∀ i x, r (C i x) = H i x) :
    r '' (⋃ i, prismEnds (C i)) = ⋃ i, prismEnds (H i) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,⟨⟨a,b⟩,rfl⟩⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,⟨(a,b),(hr i _).symm⟩⟩
  · intro hy
    obtain ⟨i,⟨⟨a,b⟩,rfl⟩⟩ := mem_iUnion.mp hy
    exact ⟨prismEndMap (C i) a b,mem_iUnion.mpr ⟨i,⟨(a,b),rfl⟩⟩,hr i _⟩

theorem finitePL_on_prism_ends
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A D : ι → Set E}
    (C : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ D i) (hC : ∀ i, (C i).IsFinitePL)
    {r : E → E} (hr : FinitePiecewiseAffineOn r (⋃ i, D i)) :
    FinitePiecewiseAffineOn r (⋃ i, prismEnds (C i)) := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_prism_endpoint_triangulation C hC
  rw [← hKs]
  exact hr.restrict K hK (hKs.subset.trans (iUnion_mono (fun i => prismEnds_subset (C i))))

end PoincareConjecture.M76.PrismBelt
