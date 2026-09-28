import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar
import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronMaps
import Mathlib.Analysis.Convex.Join









set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E}



theorem linearIndependent_of_mem_link_zero {s : Finset E} (hs : s ∈ (K.link 0).faces) :
    LinearIndependent ℝ ((↑) : s → E) := by
  have hnonzero : ∀ v ∈ (s : Set E), v ≠ (0 : E) := fun v hv h => hs.2.1 (h ▸ hv)
  have h := (linearIndependent_set_iff_affineIndependent_vadd_union_singleton
    ℝ hnonzero (0 : E)).mpr
  apply h
  let f : ↥({(0 : E)} ∪ (fun v : E => v +ᵥ (0 : E)) '' (s : Set E)) →
      ↥(insert (0 : E) s) := fun v => ⟨v.val, by simpa [vadd_eq_add] using v.property⟩
  exact (K.indep hs.2.2).comp_embedding
    ⟨f, fun x y hxy => Subtype.ext
      (congrArg (fun z : ↥(insert (0 : E) s) => (z : E)) hxy)⟩


theorem zero_notMem_link_space (K : SimplicialComplex ℝ E) : (0 : E) ∉ (K.link 0).space := by
  intro hzero
  obtain ⟨s, hs, hx⟩ := mem_space_iff.mp hzero
  exact (linearIndependent_of_mem_link_zero hs).zero_notMem_convexHull hx




theorem eq_of_normalize_eq_of_norm_le_on_link {x y : E}
    (hx : x ∈ (K.link 0).space) (hy : y ∈ (K.link 0).space)
    (hxy : NormedSpace.normalize x = NormedSpace.normalize y) (hnorm : ‖x‖ ≤ ‖y‖) : x = y := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
  have hy0 : y ≠ 0 := fun h =>
    (linearIndependent_of_mem_link_zero ht).zero_notMem_convexHull (h ▸ hyt)
  have hys : y ∈ convexHull ℝ ((insert 0 t : Finset E) : Set E) :=
    convexHull_mono (by intro z hz; exact Finset.mem_insert_of_mem hz) hyt
  have hratio : ‖x‖ / ‖y‖ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (norm_nonneg _) (norm_nonneg _), (div_le_one (norm_pos_iff.mpr hy0)).mpr hnorm⟩
  have hxeq : x = (‖x‖ / ‖y‖) • y := by
    calc
      x = ‖x‖ • NormedSpace.normalize x := (norm_smul_normalize x).symm
      _ = ‖x‖ • NormedSpace.normalize y := by rw [hxy]
      _ = (‖x‖ / ‖y‖) • y := by rw [NormedSpace.normalize, smul_smul, div_eq_mul_inv]
  have hxcone : x ∈ convexHull ℝ ((insert 0 t : Finset E) : Set E) := by
    rw [hxeq]
    exact (convex_convexHull ℝ _).smul_mem_of_zero_mem
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)) hys hratio
  have hinter := K.inter_subset_convexHull hs.1 ht.2.2 ⟨hxs, hxcone⟩
  rw [Finset.coe_insert, Set.inter_insert_of_notMem hs.2.1] at hinter
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono inter_subset_right hinter
  exact (linearIndependent_of_mem_link_zero ht).injOn_normalize_convexHull hxt hyt hxy



theorem injOn_normalize_link (K : SimplicialComplex ℝ E) :
    InjOn (NormedSpace.normalize : E → E) (K.link 0).space := by
  intro x hx y hy hxy
  rcases le_total ‖x‖ ‖y‖ with hle | hle
  · exact eq_of_normalize_eq_of_norm_le_on_link hx hy hxy hle
  · exact (eq_of_normalize_eq_of_norm_le_on_link hy hx hxy.symm hle).symm



noncomputable def radialLinkHomeomorph (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    (K.link 0).space ≃ₜ NormedSpace.normalize '' (K.link 0).space := by
  letI : CompactSpace (K.link 0).space := isCompact_iff_compactSpace.mp
    (isCompact_space_of_finite _ (finite_link_faces hK 0))
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ (injOn_normalize_link K))
  have hc : ContinuousOn (NormedSpace.normalize : E → E) (K.link 0).space := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => zero_notMem_link_space K (by simpa only [h] using hx)
    exact (continuousAt_normalize_of_ne_zero hx0).continuousWithinAt
  exact hc.domRestrict.subtype_mk _



theorem radialLinkHomeomorph_apply (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (x : (K.link 0).space) :
    (K.radialLinkHomeomorph hK x : E) = NormedSpace.normalize x.val := rfl




theorem exists_linkPoint_smul {x : E} (hx : x ∈ (K.closedStar 0).space) (hx0 : x ≠ 0) :
    ∃ y ∈ (K.link 0).space, ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have hu : (s.erase 0).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rcases (Finset.erase_eq_empty_iff s 0).mp he with he | he
    · simp [he] at hxs
    · exact hx0 (by simpa [he] using hxs)
  have hulink : s.erase 0 ∈ (K.link 0).faces :=
    ⟨K.down_closed hs.1 (Finset.erase_subset _ _) hu, Finset.notMem_erase _ _,
      K.down_closed hs.2 (Finset.insert_subset_insert _ (Finset.erase_subset _ _))
        (Finset.insert_nonempty _ _)⟩
  have hxcone : x ∈ convexHull ℝ ((insert 0 (s.erase 0) : Finset E) : Set E) :=
    convexHull_mono (Finset.insert_erase_subset _ _) hxs
  rw [Finset.coe_insert, convexHull_insert hu, mem_convexJoin] at hxcone
  obtain ⟨p, hp, y, hy, a, b, ha, hb, hab, heq⟩ := hxcone
  rw [mem_singleton_iff] at hp
  subst p
  simp only [smul_zero, zero_add] at heq
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_smul] at heq
    exact hx0 heq.symm
  exact ⟨y, convexHull_subset_space hulink hy, b, ⟨lt_of_le_of_ne hb hb0.symm, by linarith⟩,
    heq.symm⟩



theorem normalize_image_link_eq_sphere (K : SimplicialComplex ℝ E)
    (hzero : (0 : E) ∈ interior (K.closedStar 0).space) :
    NormedSpace.normalize '' (K.link 0).space = Metric.sphere (0 : E) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_normalize (fun h => zero_notMem_link_space K (by simpa only [h] using hx))
  · intro z hz
    have hznorm : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hznorm
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
    have hx : (r / 2) • z ∈ (K.closedStar 0).space := by
      apply hball
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), hznorm,
        mul_one]
      linarith
    have hx0 : (r / 2) • z ≠ 0 := smul_ne_zero (by positivity) hz0
    obtain ⟨y, hy, c, hc, hcy⟩ := exists_linkPoint_smul hx hx0
    refine ⟨y, hy, ?_⟩
    calc
      NormedSpace.normalize y = NormedSpace.normalize (c • y) :=
        (normalize_smul_of_pos hc.1 y).symm
      _ = NormedSpace.normalize ((r / 2) • z) := congrArg NormedSpace.normalize hcy.symm
      _ = NormedSpace.normalize z := normalize_smul_of_pos (by positivity) z
      _ = z := normalize_eq_self_of_norm_eq_one hznorm




noncomputable def radialLinkSphereHomeomorph (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hzero : (0 : E) ∈ interior (K.closedStar 0).space) :
    (K.link 0).space ≃ₜ Metric.sphere (0 : E) 1 :=
  (K.radialLinkHomeomorph hK).trans (Homeomorph.setCongr (K.normalize_image_link_eq_sphere hzero))



theorem radialLinkSphereHomeomorph_apply (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hzero : (0 : E) ∈ interior (K.closedStar 0).space)
    (x : (K.link 0).space) :
    (K.radialLinkSphereHomeomorph hK hzero x : E) = NormedSpace.normalize x.val := rfl

end Geometry.SimplicialComplex
