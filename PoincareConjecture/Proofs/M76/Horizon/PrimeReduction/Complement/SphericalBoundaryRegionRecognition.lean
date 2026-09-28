import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExcludedSphereBalls
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OpenPuncturedSphereConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected

set_option autoImplicit false
open Set Metric Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

theorem exists_punctured_sphere_of_spherical_frontier {ι : Type*} [Finite ι]
    (S : ι → Set V4) (e : ∀ i, S i ≃ₜ frontier Cube)
    (he : ∀ i, (e i).IsFinitePL) (hSS : ∀ i, S i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {U : Set Sphere} (hU : IsOpen U) (hUc : IsConnected U)
    (hfront : frontier U = ⋃ i, (Subtype.val : Sphere → V4) ⁻¹' S i) :
    ∃ B : ι → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (S i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ S i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (Subtype.val : Sphere → V4) '' U = Sphere \ ⋃ i, B i ∧
      (Subtype.val : Sphere → V4) '' closure U = Sphere \ ⋃ i, B i \ S i := by
  have hmiss (i : ι) : Disjoint U ((Subtype.val : Sphere → V4) ⁻¹' S i) := by
    apply disjoint_left.mpr
    intro x hx hxS
    have hf : x ∈ frontier U := hfront.symm.subset (mem_iUnion.mpr ⟨i, hxS⟩)
    exact hf.2 (hU.interior_eq.symm ▸ hx)
  have hattach (i : ι) : (Subtype.val : Sphere → V4) ⁻¹' S i ⊆ closure U :=
    (subset_iUnion (fun i => (Subtype.val : Sphere → V4) ⁻¹' S i) i).trans
      (hfront.symm.subset.trans frontier_subset_closure)
  obtain ⟨B, hB, hBU, hBd, hcl⟩ :=
    exists_original_excluded_sphere_balls S e he hSS hdis hUc hmiss hattach
  let W := Sphere \ ⋃ i, B i
  have hUW : (Subtype.val : Sphere → V4) '' U ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    intro hh
    obtain ⟨i, hi⟩ := mem_iUnion.mp hh
    exact disjoint_left.mp (hBU i) hi hx
  have hWne : W.Nonempty := (hUc.nonempty.image Subtype.val).mono hUW
  have hWconn : IsConnected W := isConnected_open_punctured_sphere B S
    (fun i => (hB i).1) (fun i => (hB i).2.1) hBd (fun i => (hB i).2.2.1) hWne
  have hWpre : IsPreconnected ((Subtype.val : Sphere → V4) ⁻¹' W) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset (by
      simpa only [Subtype.range_coe] using (sdiff_subset : W ⊆ Sphere))]
    exact hWconn.isPreconnected
  have havoid : Disjoint (frontier U) ((Subtype.val : Sphere → V4) ⁻¹' W) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hfront.subset hx)
    exact hy.2 (mem_iUnion.mpr ⟨i, (hB i).1.1 hi⟩)
  have hWU : (Subtype.val : Sphere → V4) ⁻¹' W ⊆ U := by
    apply hWpre.m76_subset_of_disjoint_frontier hU havoid
    obtain ⟨x, hx⟩ := hUc.nonempty
    exact ⟨x, hUW ⟨x, hx, rfl⟩, hx⟩
  have hUeq : (Subtype.val : Sphere → V4) '' U = W := by
    apply Subset.antisymm hUW
    intro x hx
    exact ⟨⟨x, hx.1⟩, hWU hx, rfl⟩
  refine ⟨B, fun i => ⟨(hB i).1, (hB i).2.1, (hB i).2.2.1⟩, hBd, hUeq, ?_⟩
  apply Subset.antisymm hcl
  intro x hx
  by_cases hxb : x ∈ ⋃ i, B i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hxb
    have hxS : x ∈ S i := by
      by_contra hn
      exact hx.2 (mem_iUnion.mpr ⟨i, hi, hn⟩)
    exact ⟨⟨x, hx.1⟩, hattach i hxS, rfl⟩
  · exact ⟨⟨x, hx.1⟩, subset_closure (hWU ⟨hx.1, hxb⟩), rfl⟩

end Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Cube" => closedBall (0 : V3) 1

theorem PLDomain.exists_punctured_sphere_of_spherical_frontier
    {ι κ : Type*} [Finite κ] {a : ι → OpenPartialHomeomorph Sphere V3}
    {P : Set Sphere} (hP : PLDomain a P) (hPc : IsConnected P)
    (S : κ → Set V4) (e : ∀ i, S i ≃ₜ frontier Cube)
    (he : ∀ i, (e i).IsFinitePL) (hSS : ∀ i, S i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier P = ⋃ i, (Subtype.val : Sphere → V4) ⁻¹' S i) :
    ∃ B : κ → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (S i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ S i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      (Subtype.val : Sphere → V4) '' interior P = Sphere \ ⋃ i, B i ∧
      (Subtype.val : Sphere → V4) '' P = Sphere \ ⋃ i, B i \ S i := by
  have hf : frontier (interior P) = frontier P := by
    rw [frontier, hP.closure_interior, interior_interior, frontier, hP.closed.closure_eq]
  obtain ⟨B, hB, hdisB, hint, hwhole⟩ := Set.exists_punctured_sphere_of_spherical_frontier
    S e he hSS hdis isOpen_interior (hP.isConnected_interior hPc) (hf.trans hfront)
  exact ⟨B, hB, hdisB, hint, hP.closure_interior ▸ hwhole⟩

end PoincareConjecture.M76
