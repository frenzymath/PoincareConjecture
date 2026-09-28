import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalDiskStripBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalRelativeStripFrontier
import PoincareConjecture.Proofs.M76.Rigidity.OriginalIsolatedCapCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Mathlib.CompatibleSignedPairHalfspace
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeConvexChartSides
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem exists_closedStrip_cap_halfspace_chart
    (P : OriginalDiskProduct e R j) (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {t : ℝ} (ht : t ∈ ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)) (z : D) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ P.slice t z ∈ B.source ∧ ell (B (P.slice t z)) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ x ∈ B.source, x ∈ P.closedStrip ↔ 0 ≤ ell (B x) := by
  have ht' : t = -(1 / 2 : ℝ) ∨ t = 1 / 2 := ht
  have htI : t ∈ I := by rcases ht' with h | h <;> rw [h] <;> norm_num
  have huI : -t ∈ I := by rcases ht' with h | h <;> rw [h] <;> norm_num
  have htu : t ≠ -t := by rcases ht' with h | h <;> rw [h] <;> norm_num
  obtain ⟨H, hzH, hHz, hcv, hdis, hcompat, hpair⟩ :=
    P.exists_isolated_slice_pair_chart he htI huI htu z
  have hmarks : ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ) = {t} ∪ {-t} := by
    rcases ht' with h | h <;> rw [h] <;> ext r <;> norm_num [or_comm]
  have hends : P.endDisks = (P.slice t '' D) ∪ (P.slice (-t) '' D) := by
    change P.map '' (D ×ˢ ({-(1 / 2 : ℝ), 1 / 2} : Set ℝ)) = _
    rw [hmarks, prod_union, image_union, ← P.slice_image t, ← P.slice_image (-t)]
  have hlocal (x : X) (hx : x ∈ H.source) :
      x ∈ P.endDisks ↔ x ∈ P.slice t '' D := by
    rw [hends]
    exact or_iff_left (fun hy => disjoint_left.mp hdis hx hy)
  have hpR : P.slice t z ∈ R := P.slice_inside htI z.property
  have hpfront : (⟨P.slice t z, hpR⟩ : R) ∈
      frontier ((Subtype.val : R → X) ⁻¹' P.closedStrip) := by
    rw [P.relative_frontier_closedStrip hR he hopen]
    exact hends.symm.subset (Or.inl ⟨z, z.property, rfl⟩)
  have hC : IsClosed ((Subtype.val : R → X) ⁻¹' P.closedStrip) :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed.preimage
      continuous_subtype_val
  have hselect (M : Set C3) (himage : H.IsImage R M)
      (hconvex : Convex ℝ (H.target ∩ M))
      (hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' P.closedStrip) ↔ (H x).2 = 0)) :
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ x ∈ H.source, x ∈ P.closedStrip ↔ x ∈ R ∧ 0 ≤ ε * (H x).2 := by
    rcases relative_halfspace_of_convex_frontier_chart P.closedStrip_subset hC
        (P.relative_regular_closed_closedStrip hR he hopen) hpfront H hzH
        himage hconvex hfront with h | h
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, neg_nonneg] using h⟩
  rcases hpair with ⟨hinside, hcap⟩ | ⟨hregion, hcap⟩
  · have himage : H.IsImage R univ := fun x hx =>
      ⟨fun _ => interior_subset (hinside hx), fun _ => mem_univ _⟩
    have hconvex : Convex ℝ (H.target ∩ (univ : Set C3)) := by
      simpa only [inter_univ] using hcv
    have hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' P.closedStrip) ↔ (H x).2 = 0) := by
      intro x hx
      rw [P.relative_frontier_closedStrip hR he hopen]
      exact (hlocal x hx).trans (hcap x hx)
    obtain ⟨ε, hε, hside⟩ := hselect univ himage hconvex hfront
    apply exists_compatible_halfspace_of_signed_pair e H hzH hHz
      (fun i => (hcompat i).1) ε hε
    exact Or.inl (fun x hx => (hside x hx).trans
      (and_iff_right (interior_subset (hinside hx))))
  · let a : C3 →ₗ[ℝ] ℝ :=
      (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
    let M : Set C3 := {y | 0 ≤ y.1.1}
    have himage : H.IsImage R M := fun _ hx => (hregion _ hx).symm
    have hconvex : Convex ℝ (H.target ∩ M) :=
      hcv.inter ((convex_Ici (0 : ℝ)).linear_preimage a)
    have hfront : ∀ x : R, (x : X) ∈ H.source →
        (x ∈ frontier ((Subtype.val : R → X) ⁻¹' P.closedStrip) ↔ (H x).2 = 0) := by
      intro x hx
      rw [P.relative_frontier_closedStrip hR he hopen]
      exact ((hlocal x hx).trans (hcap x hx)).trans
        (and_iff_right ((hregion x hx).mp x.property))
    obtain ⟨ε, hε, hside⟩ := hselect M himage hconvex hfront
    apply exists_compatible_halfspace_of_signed_pair e H hzH hHz
      (fun i => (hcompat i).1) ε hε
    exact Or.inr (fun x hx => (hside x hx).trans ((hregion x hx).and Iff.rfl))

theorem plDomain_closedStrip (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    PLDomain e P.closedStrip := by
  have hC : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed
  refine ⟨he.cover, he.compatible, hC, ?_⟩
  intro x hx
  by_cases hxcap : x ∈ P.endDisks
  · obtain ⟨z, hz, rfl⟩ := hxcap
    exact P.exists_closedStrip_cap_halfspace_chart hR he hopen hz.2 ⟨z.1, hz.1⟩
  · have hxlat : x ∈ P.map '' (sphere (0 : V2) 1 ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
      (P.frontier_closedStrip.subset hx).resolve_right hxcap
    have hxR : x ∈ frontier R := (P.closedStrip_inter_frontier.symm.subset hxlat).2
    have hxU : x ∈ P.openStrip := by
      by_contra hnot
      exact hxcap (P.closedStrip_sdiff_openStrip.subset ⟨hC.frontier_subset hx, hnot⟩)
    obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
    have hmem (y : R) : (y : X) ∈ U ↔ (y : X) ∈ P.openStrip := Set.ext_iff.mp hUeq y
    have hxU' : x ∈ U := (hmem ⟨x, he.closed.frontier_subset hxR⟩).mpr hxU
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hxR
    let B := H.restrOpen U hU
    refine ⟨ell, v, B, hv, ⟨hxH, hxU'⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hcompat i) hU
    · intro y hy
      change y ∈ P.closedStrip ↔ 0 ≤ ell (H y)
      constructor
      · exact fun hc => (hhalf y hy.1).mp (P.closedStrip_subset hc)
      · intro h
        have hyR := (hhalf y hy.1).mpr h
        exact image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
          ((hmem ⟨y, hyR⟩).mp hy.2)

end PoincareConjecture.M76.OriginalDiskProduct
