import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SphericalBoundaryRegionRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregionFrontier

set_option autoImplicit false
open Set Metric Geometry

namespace Geometry.CubicalThreeSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem punctured_sphere_relative_geometry {κ : Type*} [Finite κ]
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ sphere)
    (hdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hopen : ∀ i, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (A i \ r i))) :
    let Q := (Subtype.val : sphere → V4) ⁻¹' (sphere \ ⋃ i, A i \ r i)
    IsClosed Q ∧
      interior Q = (Subtype.val : sphere → V4) ⁻¹' (sphere \ ⋃ i, A i) ∧
      frontier Q = (Subtype.val : sphere → V4) ⁻¹' (⋃ i, r i) := by
  dsimp only
  let U : Set sphere := ⋃ i, (Subtype.val : sphere → V4) ⁻¹' (A i \ r i)
  have hQ : (Subtype.val : sphere → V4) ⁻¹' (sphere \ ⋃ i, A i \ r i) = Uᶜ := by
    ext x
    simp only [mem_preimage, mem_sdiff, mem_iUnion, Subtype.coe_prop, true_and,
      mem_compl_iff, U]
  have hcl : closure U = ⋃ i, (Subtype.val : sphere → V4) ⁻¹' A i := by
    rw [show U = ⋃ i, (Subtype.val : sphere → V4) ⁻¹' (A i \ r i) from rfl,
      closure_iUnion_of_finite]
    congr 1
    funext i
    exact (hA i).closure_preimage_sdiff (hAS i)
  have hi : interior Uᶜ = (Subtype.val : sphere → V4) ⁻¹' (sphere \ ⋃ i, A i) := by
    rw [interior_compl, hcl]
    ext x
    simp only [mem_compl_iff, mem_iUnion, mem_preimage, mem_sdiff, Subtype.coe_prop,
      true_and]
  rw [hQ]
  have hclosed : IsClosed Uᶜ := (isOpen_iUnion hopen).isClosed_compl
  refine ⟨hclosed, hi, ?_⟩
  rw [hclosed.frontier_eq, hi]
  ext x
  constructor
  · intro hx
    have hxA : (x : V4) ∈ ⋃ i, A i := by
      by_contra hn
      exact hx.2 ⟨x.property, hn⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    by_contra hxr
    exact hx.1 (mem_iUnion.mpr ⟨i, hxi, hxr⟩)
  · intro hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    refine ⟨?_, fun hh => hh.2 (mem_iUnion.mpr ⟨i, (hA i).1 hxi⟩)⟩
    intro hu
    obtain ⟨j, hxj, hxr⟩ := mem_iUnion.mp hu
    by_cases hji : j = i
    · exact hxr (hji.symm ▸ hxi)
    · exact disjoint_left.mp (hdis hji) hxj ((hA i).1 hxi)

end Geometry.CubicalThreeSphere
