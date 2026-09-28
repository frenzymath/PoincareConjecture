import PoincareConjecture.Proofs.M76.Rigidity.OriginalLowerIncidence
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleNormalIntervals
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDualSideRestrictions
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PairedSignedFiber
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in


theorem triangle_dualBlock_inter_boundary {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  change (T.ambient.barycentricDualBlock s).space ∩ (T.marked 1).space = ∅
  rw [T.ambient.barycentricDualBlock_space_inter_subcomplex
    (T.marked 1) (T.marked_le 1) s]
  exact (T.marked 1).barycentricDualBlock_space_eq_empty_of_not_face
    ((T.marked 2).nonempty_of_mem_faces hs) (T.disk_triangle_not_boundary hs hcard)



theorem triangle_dualRegion_inter_boundary {s : Finset (T.index → ℝ × V3)}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    T.dualRegion s ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (T.triangle_dualBlock_inter_boundary hs hcard).subset ⟨hx.1.1, hx.2⟩




theorem exists_triangle_fiber [T2Space X]
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 3) :
    ∃ F : ℝ → (T.index → ℝ × V3), FinitePiecewiseAffineOn F I ∧ InjOn F I ∧
      F '' I = T.dualRegion s ∧ F 0 = s.centroid ℝ id ∧
      (∀ r ∈ I, F r ∈ T.dualRegionRim s ↔ r ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
        0 ≤ T.height p (F r) ↔ 0 ≤ r) ∧
      ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s → ∀ r ∈ I,
        T.height p (F r) ≤ 0 ↔ r ≤ 0 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p0, hp0⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let p : (T.marked 2).vertices := ⟨p0, (T.marked 2).face_subset_vertices hs hp0⟩
  have hps : (p : T.index → ℝ × V3) ∈ s := hp0
  let N := T.ambient.barycentricDualBlock s
  have hNR : N.space ⊆ (T.marked 0).space := T.triangle_dualBlock_subset_region hs hcard
  have hN : T.dualRegion s = N.space := inter_eq_left.mpr hNR
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, _, hpair, _, hlink⟩ :=
    T.exists_triangle_normal_interval hs hcard
  have hNF : N.space ∩ (T.marked 1).space = ∅ :=
    T.triangle_dualBlock_inter_boundary hs hcard
  have hQR : (N.link (s.centroid ℝ id)).space ⊆ (T.marked 0).space := by
    rw [hlink]
    exact hpair.1.trans hNR
  have hQ : T.dualRegionRim s = {t.centroid ℝ id, u.centroid ℝ id} := by
    change ((N.link (s.centroid ℝ id)).space ∩ (T.marked 0).space) ∪
      (N.space ∩ (T.marked 1).space) = _
    rw [inter_eq_left.mpr hQR, hNF, union_empty]
    exact hlink
  have hzero : T.dualRegion s ∩ {x | T.height p x = 0} = {s.centroid ℝ id} := by
    rw [← T.triangle_base_eq_singleton hs hcard]
    ext x
    exact and_congr_right (fun hx => T.height_eq_zero_iff_on_dualRegion p hps hx)
  let ell : C3 →ₗ[ℝ] ℝ :=
    T.weight (T.chart_index p) • LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((0, 0), 1)) he
    apply T.weight_nonzero (T.chart_index p)
    change T.weight (T.chart_index p) * 1 = 0 at hz
    simpa only [mul_one] using hz
  have hstar {v : Finset (T.index → ℝ × V3)} (hv : v ∈ T.ambient.faces)
      (hsv : s ⊆ v) : v ∈ (T.ambient.closedStar p).faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hvertexzero : ∀ x ∈ s, ell (T.chart (T.chart_index p) (T.inverse x)) = 0 := by
    intro x hx
    change T.height p x = 0
    have hxD := (T.marked 2).subset_space hs hx
    exact (T.height_eq_zero_iff p
      ((T.ambient.closedStar p).subset_space (hstar (T.marked_le 2 hs) Subset.rfl) hx)
      (T.disk_space_subset_region hxD)).mpr hxD
  have hsign := (T.star_affine p).opposite_centroid_signs
    (T.star_injective p) (hstar (T.marked_le 2 hs) Subset.rfl)
    (hstar ht hst) (hstar hu hsu)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htc)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc)
    hst hsu htu ell.toAffineMap hell hvertexzero
  obtain ⟨F, hF, hi, him, h0, hrim, hpos, hneg⟩ :=
    exists_finitePL_fiber_of_paired_ends (hN.symm ▸ hpair) (T.height p)
      (T.continuousOn_height_dualRegion p hps) hzero hsign
  refine ⟨F, hF, hi, him, h0, ?_, ?_, ?_⟩
  · simpa only [hQ] using hrim
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    have heq := (T.dualRegion_halves_eq p q hs hps hqs).1
    have he : 0 ≤ T.height q (F r) ↔ 0 ≤ T.height p (F r) :=
      ⟨fun h => (heq.symm.subset ⟨hx, h⟩).2, fun h => (heq.subset ⟨hx, h⟩).2⟩
    exact he.trans (hpos r hr)
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    have heq := (T.dualRegion_halves_eq p q hs hps hqs).2
    have he : T.height q (F r) ≤ 0 ↔ T.height p (F r) ≤ 0 :=
      ⟨fun h => (heq.symm.subset ⟨hx, h⟩).2, fun h => (heq.subset ⟨hx, h⟩).2⟩
    exact he.trans (hneg r hr)

end PoincareConjecture.M76.OriginalProperDiskTriangulation
