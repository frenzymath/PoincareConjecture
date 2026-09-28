import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Simplex.SimplexGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeSphere
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Lemmas










set_option autoImplicit false

open Metric Set Topology
open scoped unitInterval

namespace Poincare.Topology



theorem exists_simplex_closedBall_pair_homeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) (hne : s.Nonempty)
    (hi : AffineIndependent ℝ ((↑) : s → E)) :
    ∃ e : closedBall (0 : Fin (s.card - 1) → ℝ) 1 ≃ₜ convexHull ℝ (s : Set E),
      ∀ x : closedBall (0 : Fin (s.card - 1) → ℝ) 1,
        ‖(x : Fin (s.card - 1) → ℝ)‖ = 1 ↔
        (e x : E) ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
  classical
  let A := affineSpan ℝ (s : Set E)
  obtain ⟨p, hp⟩ := hne
  let origin : A := ⟨p, subset_affineSpan ℝ (s : Set E) hp⟩
  let : Nonempty A := ⟨origin⟩
  have hdim : Module.finrank ℝ A.direction = s.card - 1 := by
    have hc : Fintype.card s = (s.card - 1) + 1 := by
      rw [Fintype.card_coe, Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨p, hp⟩)]
    have hr : range (Subtype.val : s → E) = (s : Set E) := by ext x; simp
    have h := hi.finrank_vectorSpan hc
    rw [hr] at h
    change Module.finrank ℝ (affineSpan ℝ (s : Set E)).direction = _
    rw [direction_affineSpan]
    exact h
  let coordinates : (Fin (s.card - 1) → ℝ) ≃ₗ[ℝ] A.direction :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hdim])
  let chart := coordinates.toAffineEquiv.trans (AffineEquiv.vaddConst ℝ origin)
  let chartHomeo := chart.toContinuousAffineEquiv.toHomeomorph
  let embedding : (Fin (s.card - 1) → ℝ) →ᵃ[ℝ] E := A.subtype.comp chart.toAffineMap
  let body := embedding ⁻¹' convexHull ℝ (s : Set E)
  have he : IsEmbedding embedding := IsEmbedding.subtypeVal.comp chartHomeo.isEmbedding
  have hcover : convexHull ℝ (s : Set E) ⊆ range embedding := by
    intro x hx
    let y : A := ⟨x, convexHull_subset_affineSpan (s : Set E) hx⟩
    refine ⟨chart.symm y, ?_⟩
    change (chart (chart.symm y) : E) = x
    rw [chart.apply_symm_apply]
  have hc : IsCompact body :=
    he.isInducing.isCompact_preimage' (s.finite_toSet.isCompact_convexHull ℝ) hcover
  have hiBody : embedding '' interior body =
      intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rw [intrinsicInterior, affineSpan_convexHull]
    exact image_interior_preimage_comp chartHomeo chartHomeo.isHomeomorph
      (Subtype.val : A → E) (convexHull ℝ (s : Set E))
  have hfBody : embedding '' frontier body =
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [intrinsicFrontier, affineSpan_convexHull]
    exact image_frontier_preimage_comp chartHomeo chartHomeo.isHomeomorph
      (Subtype.val : A → E) (convexHull ℝ (s : Set E))
  have hclBody : embedding '' closure body = convexHull ℝ (s : Set E) := by
    rw [hc.isClosed.closure_eq]
    exact image_preimage_eq_of_subset hcover
  have hneBody : (interior body).Nonempty := by
    rw [← image_nonempty (f := embedding), hiBody]
    exact Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _)
      ⟨p, subset_convexHull ℝ (s : Set E) hp⟩
  obtain ⟨rescale, _, hclosed, hsphere⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      ((convex_convexHull ℝ (s : Set E)).affine_preimage embedding) hneBody hc.isBounded
  have hclosed' : rescale.symm '' closedBall 0 1 = closure body := by
    rw [← hclosed]
    exact rescale.toEquiv.symm_image_image _
  have hsphere' : rescale.symm '' sphere 0 1 = frontier body := by
    rw [← hsphere]
    exact rescale.toEquiv.symm_image_image _
  let f := embedding ∘ rescale.symm
  have hf : IsEmbedding f := he.comp rescale.symm.isEmbedding
  have hballImage : f '' closedBall 0 1 = convexHull ℝ (s : Set E) := by
    rw [image_comp, hclosed', hclBody]
  have hsphereImage : f '' sphere 0 1 =
      intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [image_comp, hsphere', hfBody]
  let e := (hf.homeomorphImage (closedBall 0 1)).trans (Homeomorph.setCongr hballImage)
  refine ⟨e, fun x => ?_⟩
  change ‖(x : Fin (s.card - 1) → ℝ)‖ = 1 ↔
    f x ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E))
  rw [← hsphereImage]
  constructor
  · intro hx
    exact ⟨x, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    exact mem_sphere_zero_iff_norm.mp (hf.injective heq ▸ hy)


theorem stdSimplex_face_convexHull (n : ℕ) (i : Fin (n + 1)) :
    convexHull ℝ (range (fun j : {j : Fin (n + 1) // j ≠ i} =>
      Pi.single (j : Fin (n + 1)) (1 : ℝ))) =
        {z | z ∈ stdSimplex ℝ (Fin (n + 1)) ∧ z i = 0} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      exact ⟨single_mem_stdSimplex ℝ (j : Fin (n + 1)), by simp [j.property]⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨(convex_stdSimplex ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
      change a * x i + b * y i = 0
      simp only [hx.2, hy.2, mul_zero, add_zero]
  · rintro z ⟨hz, hzi⟩
    let J := Finset.univ.erase i
    have hzJ (j : Fin (n + 1)) (hj : j ∉ J) : z j = 0 := by
      have hji : j = i := by simpa [J] using hj
      simpa [hji] using hzi
    have hsum : ∑ j ∈ J, z j = 1 := by
      rw [Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => hzJ j hj)]
      exact hz.2
    have hvector : ∑ j ∈ J, z j • Pi.single j (1 : ℝ) = z := by
      calc
        _ = ∑ j, z j • Pi.single j (1 : ℝ) := by
          apply Finset.sum_subset (Finset.subset_univ J)
          intro j _ hj
          rw [hzJ j hj, zero_smul]
        _ = z := by
          ext k
          simp [Finset.sum_apply, Pi.single_apply]
    have hmem := J.centerMass_mem_convexHull (z := fun j => Pi.single j (1 : ℝ))
      (s := range (fun k : {k : Fin (n + 1) // k ≠ i} => Pi.single (k : Fin (n + 1)) 1))
      (fun j _ => hz.1 j)
      (show 0 < ∑ j ∈ J, z j by rw [hsum]; exact zero_lt_one)
      (fun j hj => ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, rfl⟩)
    rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hvector] at hmem


theorem stdSimplex_intrinsicFrontier (n : ℕ) :
    intrinsicFrontier ℝ (stdSimplex ℝ (Fin (n + 1))) =
      {z | z ∈ stdSimplex ℝ (Fin (n + 1)) ∧ ∃ i, z i = 0} := by
  classical
  let : DecidableEq (Fin (n + 1) → ℝ) := Classical.decEq _
  let v : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun i => Pi.single i 1
  let s := Finset.univ.image v
  have hi : AffineIndependent ℝ v :=
    (Pi.linearIndependent_single_one (Fin (n + 1)) ℝ).affineIndependent
  have hset : (s : Set (Fin (n + 1) → ℝ)) = range v := by simp [s]
  have hne : s.Nonempty := by simp [s]
  have his : AffineIndependent ℝ ((↑) : s → (Fin (n + 1) → ℝ)) := by
    change AffineIndependent ℝ (Subtype.val : ↥(s : Set (Fin (n + 1) → ℝ)) → _)
    rw [hset]
    exact hi.range
  have hhull : convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) =
      stdSimplex ℝ (Fin (n + 1)) := by
    rw [hset]
    exact convexHull_rangle_single_eq_stdSimplex ℝ _
  have herase (i : Fin (n + 1)) :
      (s.erase (v i) : Set (Fin (n + 1) → ℝ)) =
        range (fun j : {j : Fin (n + 1) // j ≠ i} => v j) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxi, hxs⟩ := Finset.mem_erase.mp hx
      have hxr : x ∈ range v := by rw [← hset]; exact hxs
      obtain ⟨j, rfl⟩ := hxr
      exact ⟨⟨j, fun h => hxi (congrArg v h)⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      refine Finset.mem_erase.mpr ⟨fun h => j.property (hi.injective h), ?_⟩
      change v j ∈ (s : Set (Fin (n + 1) → ℝ))
      rw [hset]
      exact mem_range_self (j : Fin (n + 1))
  rw [← hhull, simplex_intrinsicFrontier s hne his]
  ext z
  constructor
  · intro hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    have hir : (i : Fin (n + 1) → ℝ) ∈ range v := by rw [← hset]; exact i.property
    obtain ⟨j, hj⟩ := hir
    rw [← hj, herase, stdSimplex_face_convexHull] at hzi
    exact ⟨hhull.symm ▸ hzi.1, j, hzi.2⟩
  · rintro ⟨hz, i, hzi⟩
    have hvi : v i ∈ s := by
      change v i ∈ (s : Set (Fin (n + 1) → ℝ))
      rw [hset]
      exact mem_range_self i
    refine mem_iUnion.mpr ⟨⟨v i, hvi⟩, ?_⟩
    change z ∈ convexHull ℝ (s.erase (v i) : Set (Fin (n + 1) → ℝ))
    rw [herase, stdSimplex_face_convexHull]
    exact ⟨hhull ▸ hz, hzi⟩


theorem exists_stdSimplex_closedBall_pair_homeomorph (n : ℕ) :
    ∃ e : stdSimplex ℝ (Fin (n + 1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1,
      ∀ z : stdSimplex ℝ (Fin (n + 1)),
        (∃ i, z i = 0) ↔ ‖(e z : Fin n → ℝ)‖ = 1 := by
  classical
  let v : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun i => Pi.single i 1
  let s := Finset.univ.image v
  have hi : AffineIndependent ℝ v :=
    (Pi.linearIndependent_single_one (Fin (n + 1)) ℝ).affineIndependent
  have hset : (s : Set (Fin (n + 1) → ℝ)) = range v := by simp [s]
  have hne : s.Nonempty := by simp [s]
  have his : AffineIndependent ℝ ((↑) : s → (Fin (n + 1) → ℝ)) := by
    change AffineIndependent ℝ (Subtype.val : ↥(s : Set (Fin (n + 1) → ℝ)) → _)
    rw [hset]
    exact hi.range
  have hcard : s.card = n + 1 := by
    rw [Finset.card_image_of_injective _ hi.injective, Finset.card_univ, Fintype.card_fin]
  have hhull : convexHull ℝ (s : Set (Fin (n + 1) → ℝ)) =
      stdSimplex ℝ (Fin (n + 1)) := by
    rw [hset]
    exact convexHull_rangle_single_eq_stdSimplex ℝ _
  have h := exists_simplex_closedBall_pair_homeomorph s hne his
  rw [hcard, Nat.add_sub_cancel, hhull] at h
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun z => ?_⟩
  have hz := he (e.symm z)
  rw [e.apply_symm_apply, stdSimplex_intrinsicFrontier] at hz
  exact ⟨fun ⟨i, hi⟩ => hz.mpr ⟨z.property, i, hi⟩, fun h => (hz.mp h).2⟩


theorem exists_stdSimplex_cube_pair_homeomorph (n : ℕ) :
    ∃ e : stdSimplex ℝ (Fin (n + 1)) ≃ₜ (I^(Fin n)),
      ∀ z : stdSimplex ℝ (Fin (n + 1)),
        (∃ i, z i = 0) ↔ e z ∈ Cube.boundary (Fin n) := by
  obtain ⟨e, he⟩ := exists_stdSimplex_closedBall_pair_homeomorph n
  obtain ⟨g, _, hg⟩ := exists_cube_closedBall_homeomorph (N := Fin n)
  refine ⟨e.trans g.symm, fun z => ?_⟩
  change (∃ i, z i = 0) ↔ g.symm (e z) ∈ Cube.boundary (Fin n)
  rw [he]
  simpa only [g.apply_symm_apply] using (hg (g.symm (e z))).symm

end Poincare.Topology
