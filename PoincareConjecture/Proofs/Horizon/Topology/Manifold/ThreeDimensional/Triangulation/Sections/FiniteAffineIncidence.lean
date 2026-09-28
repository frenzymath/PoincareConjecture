import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteConvexBall
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false

open Set Metric
open scoped BigOperators Topology

universe u v

namespace Poincare.Topology

theorem exists_small_convex_support_of_linear_max
    {E : Type u} [AddCommGroup E] [Module Real E] [FiniteDimensional Real E]
    (s : Finset E) (y : E) (hy : y ∈ convexHull Real (s : Set E))
    (l : E →ₗ[Real] Real) (hlne : l ≠ 0)
    (hmax : ∀ z ∈ s, l z ≤ l y) :
    ∃ t : Finset E, t ⊆ s ∧ t.card ≤ Module.finrank Real E ∧
      y ∈ convexHull Real (t : Set E) := by
  classical
  obtain ⟨I, hI, z, w, hz, hind, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  let := hI
  have hweighted : ∑ i, w i * l (z i) = l y := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg l hwz
  have hdeficit : ∑ i, w i * (l y - l (z i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweighted, hwsum,
      one_mul, sub_self]
  have hlevel (i : I) : l (z i) = l y := by
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        mul_nonneg (hwpos j).le
          (sub_nonneg.mpr (hmax (z j) (hz (mem_range_self j)))))).mp hdeficit i
        (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (hwpos i).ne')).symm
  have hspan : vectorSpan Real (Set.range z) ≤ LinearMap.ker l := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, ⟨i, rfl⟩, q, ⟨j, rfl⟩, rfl⟩
    change l (z i - z j) = 0
    rw [map_sub, hlevel, hlevel, sub_self]
  have hcard : Fintype.card I ≤ Module.finrank Real E := by
    have hc := hind.card_le_finrank_succ
    have hm := Submodule.finrank_mono hspan
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hlne
    omega
  let t : Finset E := Finset.univ.image z
  have hts : t ⊆ s := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hz (mem_range_self i)
  refine ⟨t, hts, (Finset.card_image_le.trans hcard), ?_⟩
  exact mem_convexHull_of_exists_fintype w z (fun i => (hwpos i).le) hwsum
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hwz

theorem exists_minimal_affine_section_face_through_vertex
    {E : Type u} [AddCommGroup E] [Module Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0)
    (v : E) (hv : v ∈ s) :
    ∃ t : Finset E, t ⊆ s ∧ v ∈ t ∧ t.card = Module.finrank Real F + 1 ∧
      ∃ x ∈ convexHull Real (t : Set E), A x = 0 := by
  classical
  by_cases hAv : A v = 0
  · have hdim : Module.finrank Real F = 0 := by
      by_contra hdim
      have hcard : ({v} : Finset E).card ≤ Module.finrank Real F := by
        simpa using Nat.one_le_iff_ne_zero.mpr hdim
      have h := hgap {v} (by simpa using hv) hcard v (by simp)
      rw [hAv, norm_zero] at h
      exact (not_le_of_gt ha) h
    exact ⟨{v}, by simpa using hv, by simp, by simp [hdim], v, by simp, hAv⟩
  let C : Set F := convexHull Real (↑(s.image A) : Set F)
  have hCcompact : IsCompact C := (s.image A).finite_toSet.isCompact_convexHull Real
  have hCzero : (0 : F) ∈ C := by
    dsimp only [C]
    rw [Finset.coe_image, ← A.image_convexHull]
    exact hzero
  have hCball : closedBall (0 : F) a ⊆ C := by
    simpa only [C, A.image_convexHull, Finset.coe_image] using
      closedBall_subset_affine_convexHull_of_small_faces_gap A s a ha hgap hzero
  have hCnhds : C ∈ 𝓝 (0 : F) :=
    Filter.mem_of_superset (ball_mem_nhds _ ha)
      (ball_subset_closedBall.trans hCball)
  have hCabs : Absorbent Real C := absorbent_nhds_zero hCnhds
  have hCbdd : Bornology.IsVonNBounded Real C :=
    (NormedSpace.isVonNBounded_iff Real).mpr hCcompact.isBounded
  let c := gauge C (-(A v))
  have hc : 0 < c := (gauge_pos hCabs hCbdd).mpr (neg_ne_zero.mpr hAv)
  let y : F := c⁻¹ • (-(A v))
  have hgy : gauge C y = 1 := by
    dsimp only [y]
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hc.le)]
    exact inv_mul_cancel₀ hc.ne'
  have hyfront : y ∈ frontier C :=
    mem_frontier_of_gauge_eq_one (convex_convexHull Real _) hCzero hCabs hgy
  have hyC : y ∈ C := by
    simpa only [hCcompact.isClosed.closure_eq] using hyfront.1
  obtain ⟨l, hlne, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull Real (↑(s.image A) : Set F)) hyfront.2
      ⟨0, mem_interior_iff_mem_nhds.mpr hCnhds⟩
  have hlinear : l.toLinearMap ≠ 0 := by
    intro h
    apply hlne
    ext z
    exact LinearMap.congr_fun h z
  obtain ⟨t, hts, htcard, hyt⟩ := exists_small_convex_support_of_linear_max
    (s.image A) y hyC l.toLinearMap hlinear
      (fun z hz => hmax z (subset_convexHull Real _ hz))
  have hpre (q : t) : ∃ p ∈ s, A p = (q : F) :=
    Finset.mem_image.mp (hts q.property)
  choose p hps hpA using hpre
  let r : Finset E := Finset.univ.image p
  have hrs : r ⊆ s := by
    intro z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
    exact hps q
  have hrcard : r.card ≤ Module.finrank Real F := by
    calc
      r.card ≤ Fintype.card t := Finset.card_image_le
      _ = t.card := Fintype.card_coe _
      _ ≤ Module.finrank Real F := htcard
  have hArt : A '' (r : Set E) = (t : Set F) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
      rw [hpA q]
      exact q.property
    · intro hz
      exact ⟨p ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩,
        hpA ⟨z, hz⟩⟩
  let R := insert v r
  have hRs : R ⊆ s := Finset.insert_subset hv hrs
  have hrR : r ⊆ R := Finset.subset_insert _ _
  have hvR : A v ∈ convexHull Real (A '' (R : Set E)) :=
    subset_convexHull Real _ (mem_image_of_mem A (Finset.mem_insert_self _ _))
  have hyR : y ∈ convexHull Real (A '' (R : Set E)) := by
    apply convexHull_mono (Set.image_mono hrR)
    rw [hArt]
    exact hyt
  have hc1 : 0 < c + 1 := by linarith
  have hsum : (c + 1)⁻¹ + c / (c + 1) = 1 := by
    field_simp
    ring
  have hcomb : (c + 1)⁻¹ • A v + (c / (c + 1)) • y = 0 := by
    dsimp only [y]
    rw [smul_smul, smul_neg, ← sub_eq_add_neg]
    have heq : c / (c + 1) * c⁻¹ = (c + 1)⁻¹ := by
      field_simp
    rw [heq, sub_self]
  have hRzero : ∃ x ∈ convexHull Real (R : Set E), A x = 0 := by
    have hz := (convex_convexHull Real (A '' (R : Set E))) hvR hyR
      (inv_nonneg.mpr hc1.le) (div_nonneg hc.le hc1.le) hsum
    rw [hcomb, ← A.image_convexHull] at hz
    exact hz
  have hRcard : R.card = Module.finrank Real F + 1 := by
    have hu : R.card ≤ Module.finrank Real F + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hrcard 1)
    have hl : Module.finrank Real F < R.card := by
      by_contra h
      obtain ⟨x, hx, hx0⟩ := hRzero
      have hg := hgap R hRs (Nat.le_of_not_gt h) x hx
      rw [hx0, norm_zero] at hg
      exact (not_le_of_gt ha) hg
    omega
  exact ⟨R, hRs, Finset.mem_insert_self _ _, hRcard, hRzero⟩

end Poincare.Topology
