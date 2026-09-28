import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierPLNormalization
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull









set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_finitePL_frontier_cap_flattening (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hs0 : (0 : E) ∈ interior s) (L : E →ₗ[ℝ] ℝ)
    (hspace : K.space = frontier s ∩ {x | 1 ≤ L x}) :
    ∃ e : (frontier s ∩ {x | 1 ≤ L x} : Set E) ≃ₜ (s ∩ {x | L x = 1} : Set E),
      e.IsFinitePL ∧
      (∀ x : (frontier s ∩ {x | 1 ≤ L x} : Set E),
        L (x : E) = 1 → (e x : E) = x) ∧
      (∀ x : (frontier s ∩ {x | 1 ≤ L x} : Set E),
        L (x : E) = 1 ↔ (e x : E) ∈ frontier s) := by
  classical
  have hKfront : K.space ⊆ frontier s := hspace.subset.trans inter_subset_left
  have hlin := K.linearIndependent_faces_of_space_subset_frontier hcv hs0 hKfront
  have hinj := (hcv.injOn_normalize_frontier hs0).mono hKfront
  let r : E → ℝ := fun x => (L x)⁻¹
  have hLx (x : E) (hx : x ∈ K.space) : 1 ≤ L x := (hspace ▸ hx).2
  have hr (x : E) (hx : x ∈ K.vertices) : 0 < r x :=
    inv_pos.mpr (zero_lt_one.trans_le (hLx x (K.vertices_subset_space hx)))
  let R := K.radialRescale hlin hinj r hr
  have hvertex (x : E) (hx : x ∈ K.space) : r x • x ∈ s ∩ {y | L y = 1} := by
    have hp : 0 < L x := zero_lt_one.trans_le (hLx x hx)
    have hle : r x ≤ 1 := (inv_le_one₀ hp).mpr (hLx x hx)
    refine ⟨?_, ?_⟩
    · simpa only [smul_zero, zero_add] using hcv (interior_subset hs0)
        (hs.isClosed.frontier_subset (hKfront hx))
        (sub_nonneg.mpr hle) (inv_nonneg.mpr hp.le) (sub_add_cancel 1 (r x))
    · change L ((L x)⁻¹ • x) = 1
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']
  have hRsub : R.space ⊆ s ∩ {x | L x = 1} := by
    intro y hy
    obtain ⟨_, ⟨u, hu, rfl⟩, hyu⟩ := mem_space_iff.mp hy
    rw [Finset.coe_image] at hyu
    exact convexHull_min (by
      rintro _ ⟨v, hv, rfl⟩
      exact hvertex v (K.subset_space hu hv))
      (hcv.inter ((convex_singleton (1 : ℝ)).linear_preimage L)) hyu
  have hRspace : R.space = s ∩ {x | L x = 1} := by
    apply Subset.antisymm hRsub
    rintro y ⟨hyS, hyL⟩
    have hy0 : y ≠ 0 := by intro he; simp [he] at hyL
    obtain ⟨x, hx, a, ha, hya⟩ := hs.exists_frontier_pos_smul hcv hs0 hyS hy0
    have hprod : a * L x = 1 := by
      simpa only [mem_ofPred_eq, hya, map_smul, smul_eq_mul] using hyL
    have hxp : 0 < L x := (mul_pos_iff.mp (hprod.symm ▸ zero_lt_one)).resolve_right
      (fun h => (not_lt_of_ge ha.1.le) h.1) |>.2
    have hxL : 1 ≤ L x := by nlinarith [mul_le_mul_of_nonneg_right ha.2 hxp.le]
    have hxK : x ∈ K.space := hspace.symm ▸ And.intro hx hxL
    have hxy : NormedSpace.normalize x = NormedSpace.normalize y := by
      rw [hya, normalize_smul_of_pos ha.1]
    have hnorm : NormedSpace.normalize y ∈ NormedSpace.normalize '' R.space := by
      rw [K.normalize_image_radialRescale_space hlin hinj r hr]
      exact ⟨x, hxK, hxy⟩
    obtain ⟨z, hz, hzy⟩ := hnorm
    have heq : z = y := L.injOn_normalize_of_eq_one
      (s := s ∩ {x | L x = 1}) (fun _ hw => hw.2) (hRsub hz) ⟨hyS, hyL⟩ hzy
    exact heq ▸ hz
  obtain ⟨f, _, e, hf, _, hfv, hef, _⟩ :=
    K.exists_radialRescale_homeomorph hK hlin hinj r hr
  have hfix (x : E) (hx : x ∈ K.space) (hxL : L x = 1) : f x = x := by
    obtain ⟨u, hu, hxu⟩ := mem_space_iff.mp hx
    let A : E →ᵃ[ℝ] ℝ := L.toAffineMap - AffineMap.const ℝ E 1
    let v := u.filter (fun z => A z = 0)
    have hxv : x ∈ convexHull ℝ (v : Set E) := by
      have hv : (v : Set E) = (u : Set E) ∩ {z | A z = 0} := by
        ext z
        simp only [v, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
      rw [hv]
      exact u.mem_convexHull_zero_vertices A
        (fun z hz => sub_nonneg.mpr (hLx z (K.subset_space hu hz))) hxu
        (by change L x - 1 = 0; rw [hxL, sub_self])
    have hvne := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxv⟩)
    have hvK := K.down_closed hu (Finset.filter_subset _ _) hvne
    obtain ⟨a, ha⟩ := hf v hvK
    have hav (z : E) (hz : z ∈ v) : a z = z := by
      have hzA := (Finset.mem_filter.mp hz).2
      have hzL : L z = 1 := sub_eq_zero.mp hzA
      rw [← ha (subset_convexHull ℝ _ hz), hfv (K.face_subset_vertices hvK hz)]
      simp only [r, hzL, inv_one, one_smul]
    exact (ha hxv).trans ((AffineMap.eqOn_affineSpan
      (f := a.toAffineMap) (g := AffineMap.id ℝ E) hav) (convexHull_subset_affineSpan _ hxv))
  let G := (Homeomorph.setCongr hspace.symm).trans (e.trans (Homeomorph.setCongr hRspace))
  have he : e.IsFinitePL := ⟨f, ⟨K, hK, rfl, hf⟩, hef⟩
  have hGval (x : (frontier s ∩ {x | 1 ≤ L x} : Set E)) : (G x : E) = f x :=
    hef ⟨x, hspace.symm ▸ x.property⟩
  have hGfix (x : (frontier s ∩ {x | 1 ≤ L x} : Set E)) (hxL : L (x : E) = 1) :
      (G x : E) = x := (hGval x).trans (hfix x (hspace.symm ▸ x.property) hxL)
  refine ⟨G, he.setCongr hspace hRspace, hGfix, fun x => ?_⟩
  constructor
  · intro hx
    rw [hGfix x hx]
    exact x.property.1
  · intro hx
    let z : (frontier s ∩ {x | 1 ≤ L x} : Set E) := ⟨G x, hx, (G x).property.2.ge⟩
    have hGz : G z = G x := Subtype.ext (hGfix z (G x).property.2)
    have hz : (z : E) = x := congrArg Subtype.val (G.injective hGz)
    exact hz ▸ (G x).property.2

end Geometry.SimplicialComplex
