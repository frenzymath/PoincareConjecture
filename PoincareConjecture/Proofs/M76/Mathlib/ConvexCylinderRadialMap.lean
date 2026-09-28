import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierRadialData
import PoincareConjecture.Proofs.M76.Mathlib.ConvexCylinderRadialGeometry
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finitePL_nested_cylinder_frontier_map
    (K : SimplicialComplex ℝ (E × ℝ)) (hK : K.faces.Finite)
    {Q C : Set E} (hQ : IsCompact Q) (hC : IsCompact C)
    (hQcv : Convex ℝ Q) (hCcv : Convex ℝ C)
    (hQ0 : (0 : E) ∈ interior Q) (hQC : Q ⊆ interior C)
    (hspace : K.space = frontier (C ×ˢ Icc (-1 : ℝ) 1))
    {ι : Type*} [Finite ι] (L : ι → E →ₗ[ℝ] ℝ)
    (hL : ∀ i, L i ≠ 0) (hrep : Q = {x | ∀ i, L i x ≤ 1}) :
    ∃ (f : E × ℝ → E × ℝ)
      (e : frontier (C ×ˢ Icc (-1 : ℝ) 1) ≃ₜ frontier (Q ×ˢ Icc (-1 : ℝ) 2)),
      FinitePiecewiseAffineOn f (frontier (C ×ˢ Icc (-1 : ℝ) 1)) ∧
      e.IsFinitePL ∧ (∀ x, (e x : E × ℝ) = f x) ∧
      MapsTo f (Q ×ˢ {(1 : ℝ)}) {y | 1 ≤ y.2} ∧
      MapsTo f (frontier (C ×ˢ Icc (-1 : ℝ) 1) \ interior Q ×ˢ {1})
        {y | y.2 ≤ 1} := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let A (i : ι) : (E × ℝ) →ᵃ[ℝ] ℝ :=
    ((L i).comp (LinearMap.fst ℝ E ℝ)).toAffineMap - AffineMap.const ℝ (E × ℝ) 1
  let T : (E × ℝ) →ᵃ[ℝ] ℝ :=
    AffineMap.const ℝ (E × ℝ) 1 - (LinearMap.snd ℝ E ℝ).toAffineMap
  let B : (E × ℝ) →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ E ℝ).toAffineMap + AffineMap.const ℝ (E × ℝ) 1
  let H := (Finset.univ.image A ∪ Finset.univ.image (fun i => -A i)) ∪ {T, B}
  let N := hK.toFinset.sup Finset.card
  have hN (u : Finset (E × ℝ)) (hu : u ∈ K.faces) : u.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hu)).trans (Nat.le_succ N)
  obtain ⟨J, hJ, hJK, _, hJH⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN H
  have hCs0 : (0 : E × ℝ) ∈ interior (C ×ˢ Icc (-1 : ℝ) 1) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hQC (interior_subset hQ0), by norm_num, by norm_num⟩
  have hQt0 : (0 : E × ℝ) ∈ interior (Q ×ˢ Icc (-1 : ℝ) 2) := by
    rw [interior_prod_eq, interior_Icc]
    exact ⟨hQ0, by norm_num, by norm_num⟩
  obtain ⟨D, hD, hDJ, f, hf, hfv, e, he, hef⟩ :=
    J.exists_finitePL_convex_frontier_radial_data hJ
      (hC.prod isCompact_Icc) (hQ.prod isCompact_Icc)
      (hCcv.prod (convex_Icc _ _)) (hQcv.prod (convex_Icc _ _))
      hCs0 hQt0 (hJK.space_eq.trans hspace) (LinearMap.cylinderUnitForms L)
      (LinearMap.cylinderUnitForms_ne_zero L hL)
      (LinearMap.cylinderUnitForms_region L hrep)
  have hDs : D.space = frontier (C ×ˢ Icc (-1 : ℝ) 1) :=
    hDJ.space_eq.trans (hJK.space_eq.trans hspace)
  have hDH (F : (E × ℝ) →ᵃ[ℝ] ℝ) (hF : F ∈ H) : D.RespectsAffineHyperplane F :=
    hDJ.respectsAffineHyperplane (hJH F hF)
  have hDA (i : ι) : D.RespectsAffineHyperplane (A i) := hDH _ (by simp [H])
  have hDnA (i : ι) : D.RespectsAffineHyperplane (-A i) := hDH _ (by simp [H])
  have hDT : D.RespectsAffineHyperplane T := hDH _ (by simp [H])
  have hDB : D.RespectsAffineHyperplane B := hDH _ (by simp [H])
  let r (v : E × ℝ) : ℝ := (gauge (Q ×ˢ Icc (-1 : ℝ) 2) v)⁻¹
  have hrad (v : E × ℝ) (hv : v ∈ D.vertices) :
      0 < r v ∧ r v • v ∈ frontier (Q ×ˢ Icc (-1 : ℝ) 2) := by
    apply (hQ.prod isCompact_Icc).gauge_inv_smul_mem_frontier
      (hQcv.prod (convex_Icc _ _)) hQt0
    intro heq
    have hvf := hDs.subset (D.vertices_subset_space hv)
    exact hvf.2 (heq ▸ hCs0)
  have hbounds (v : E × ℝ) (hv : v ∈ D.vertices) : -1 ≤ v.2 ∧ v.2 ≤ 1 :=
    ((hC.isClosed.prod isClosed_Icc).frontier_subset
      (hDs.subset (D.vertices_subset_space hv))).2
  have hfx (v : E × ℝ) (hv : v ∈ D.vertices) : f v = r v • v := hfv hv
  have hfinit : FinitePiecewiseAffineOn f (frontier (C ×ˢ Icc (-1 : ℝ) 1)) := by
    rw [← hDs]
    exact hf.finitePiecewiseAffineOn hD
  refine ⟨f, e, hfinit, he, hef, ?_, ?_⟩
  · let U := Finset.univ.image A ∪ {T}
    have hDU : ∀ F ∈ U, D.RespectsAffineHyperplane F := by
      intro F hF
      rcases Finset.mem_union.mp hF with hF | hF
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hF
        exact hDA i
      · have heq : F = T := Finset.mem_singleton.mp hF
        subst F
        exact hDT
    intro x hx
    refine hf.mapsTo_of_aligned_halfspaces U hDU
      ((convex_Ici (1 : ℝ)).affine_preimage (LinearMap.snd ℝ E ℝ).toAffineMap)
      ?_ x
      (hDs.symm.subset (prod_singleton_one_subset_frontier_cylinder
        (hQC.trans interior_subset) hx)) ?_
    · intro v hv hvU
      have hvQ : v.1 ∈ Q := by
        apply hrep.symm.subset
        intro i
        have h := hvU (A i) (by simp [U])
        change L i v.1 - 1 ≤ 0 at h
        linarith
      have hvone : v.2 = 1 := by
        have h := hvU T (by simp [U])
        change 1 - v.2 ≤ 0 at h
        exact le_antisymm (hbounds v hv).2 (by linarith)
      have hvtop : v = (v.1, (1 : ℝ)) := Prod.ext rfl hvone
      have hone := hQcv.one_le_of_smul_top_mem_frontier_cylinder hQ0 hvQ
        (hrad v hv).1 (by simpa only [← hvtop] using (hrad v hv).2)
      change 1 ≤ (f v).2
      rw [hfx v hv]
      change 1 ≤ r v * v.2
      simpa only [hvone, mul_one] using hone
    · intro F hF
      rcases Finset.mem_union.mp hF with hF | hF
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hF
        change L i x.1 - 1 ≤ 0
        exact sub_nonpos.mpr ((hrep.subset hx.1) i)
      · have heq : F = T := Finset.mem_singleton.mp hF
        subst F
        change 1 - x.2 ≤ 0
        rw [show x.2 = 1 from hx.2]
        norm_num
  · intro x hx
    have hxD : x ∈ D.space := hDs.symm.subset hx.1
    have hconv : Convex ℝ {y : E × ℝ | y.2 ≤ 1} :=
      (convex_Iic (1 : ℝ)).affine_preimage (LinearMap.snd ℝ E ℝ).toAffineMap
    rcases bottom_or_not_mem_inner_of_mem_cylinderExterior hQC hx with hbottom | hout
    · refine hf.mapsTo_of_aligned_halfspaces {B}
        (by intro F hF; simpa only [Finset.mem_singleton.mp hF] using hDB)
        hconv ?_ x hxD ?_
      · intro v hv hvB
        have h := hvB B (by simp)
        change v.2 + 1 ≤ 0 at h
        have hvbottom : v.2 = -1 := le_antisymm (by linarith) (hbounds v hv).1
        change (f v).2 ≤ 1
        rw [hfx v hv]
        change r v * v.2 ≤ 1
        rw [hvbottom]
        linarith [(hrad v hv).1]
      · intro F hF
        have heq : F = B := Finset.mem_singleton.mp hF
        subst F
        change x.2 + 1 ≤ 0
        rw [hbottom]
        norm_num
    · obtain ⟨i, hi⟩ := exists_unit_le_of_not_mem_interior L hL hrep hout
      refine hf.mapsTo_of_aligned_halfspaces {-A i}
        (by intro F hF; simpa only [Finset.mem_singleton.mp hF] using hDnA i)
        hconv ?_ x hxD ?_
      · intro v hv hvA
        have h := hvA (-A i) (by simp)
        change -(L i v.1 - 1) ≤ 0 at h
        have hvunit : 1 ≤ L i v.1 := by linarith
        have hbase : r v • v.1 ∈ Q :=
          ((hQ.isClosed.prod isClosed_Icc).frontier_subset (hrad v hv).2).1
        have hunit : L i (r v • v.1) ≤ 1 := (hrep.subset hbase) i
        change (f v).2 ≤ 1
        rw [hfx v hv]
        exact (L i).mul_height_le_one_of_unit_le (hrad v hv).1.le
          (hbounds v hv).2 hvunit hunit
      · intro F hF
        have heq : F = -A i := Finset.mem_singleton.mp hF
        subst F
        change -(L i x.1 - 1) ≤ 0
        linarith

end Geometry.SimplicialComplex
