import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SegmentGermDegree
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

theorem ncard_neighborSet_eq_two_of_local_segments_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ a ∈ K.faces, a.card ≤ 2)
    (hzero : (0 : E) ∈ K.vertices) {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0})
    (hlocal : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ K.space ↔ x ∈ segment ℝ 0 u ∪ segment ℝ 0 v) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet ⟨0, hzero⟩).ncard = 2 := by
  have hlocal' : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ K.space ∩ {y | (0 : E →ₗ[ℝ] ℝ) y = 0} ↔
        x ∈ segment ℝ 0 u ∪ segment ℝ 0 v := by
    simpa using hlocal
  have hcard : (K.link 0).space.ncard = 2 := by
    simpa using K.ncard_link_zero_of_local_segments hK hzero
      (0 : E →ₗ[ℝ] ℝ) hu hv hinter hlocal'
  have hvertices : (K.link 0).space = (K.link 0).vertices := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp hx
      have hle := hbound (insert 0 a) ha.2.2
      rw [Finset.card_insert_of_notMem ha.2.1] at hle
      have hpos := Finset.card_pos.mpr ((K.link 0).nonempty_of_mem_faces ha)
      have hacard : a.card = 1 := by omega
      obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp hacard
      have hxw : x = w := by simpa using hxa
      exact hxw.symm ▸ ha
    · exact (K.link 0).vertices_subset_space
  rw [K.ncard_edgeGraph_neighborSet, K.faceLink_singleton_eq_link, ← hvertices]
  exact hcard

theorem ncard_neighborSet_eq_two_of_local_segments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ a ∈ K.faces, a.card ≤ 2)
    {p u v : E} (hp : p ∈ K.vertices) (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ K.space ↔ x ∈ segment ℝ p u ∪ segment ℝ p v) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hp⟩).ncard = 2 := by
  let A : E →ᴬ[ℝ] E := ContinuousAffineMap.id ℝ E - ContinuousAffineMap.const ℝ E p
  have hAi : Function.Injective A := by
    intro x y h
    change x - p = y - p at h
    simpa only [sub_add_cancel] using congrArg (fun z => z + p) h
  have hf : K.AffineOnFaces A := K.affineOnFaces_affine A
  let R := hf.embeddedImage hAi.injOn
  have hR : R.faces.Finite := hf.embeddedImage_finite hAi.injOn hK
  have hAp : A p = 0 := by simp [A]
  have hzero : (0 : E) ∈ R.vertices := by
    have h := (hf.image_mem_embeddedImage_iff hAi.injOn (K.subset_space hp)).mpr hp
    change ({0} : Finset E) ∈ R.faces
    simpa only [Finset.image_singleton, hAp] using h
  have hRbound : ∀ a ∈ R.faces, a.card ≤ 2 := by
    intro a ha
    rw [hf.embeddedImage_faces hAi.injOn] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    exact Finset.card_image_le.trans (hbound b hb)
  have hRs : R.space = (fun x => x - p) '' K.space := hf.embeddedImage_space hAi.injOn
  have hmem (T : Set E) (x : E) : x ∈ (fun t => t - p) '' T ↔ x + p ∈ T := by
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa only [sub_add_cancel] using ht
    · intro hx
      exact ⟨x + p, hx, add_sub_cancel_right x p⟩
  have hseg (w : E) : (fun x => x - p) '' segment ℝ p w = segment ℝ 0 (w - p) := by
    have h := image_segment ℝ A.toAffineMap p w
    change (fun x => x - p) '' segment ℝ p w = segment ℝ (p - p) (w - p) at h
    simpa only [sub_self] using h
  have hinter' : segment ℝ 0 (u - p) ∩ segment ℝ 0 (v - p) ⊆ {0} := by
    intro x hx
    have hu' : x + p ∈ segment ℝ p u := (hmem _ x).mp ((hseg u).symm.subset hx.1)
    have hv' : x + p ∈ segment ℝ p v := (hmem _ x).mp ((hseg v).symm.subset hx.2)
    have he : x + p = p := hinter ⟨hu', hv'⟩
    exact add_right_cancel (he.trans (zero_add p).symm)
  have hc : Tendsto (fun x : E => x + p) (𝓝 0) (𝓝 p) := by
    have hc' : Continuous (fun x : E => x + p) := continuous_id.add continuous_const
    simpa only [zero_add] using hc'.tendsto (0 : E)
  have hlocalR : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ R.space ↔ x ∈ segment ℝ 0 (u - p) ∪ segment ℝ 0 (v - p) := by
    filter_upwards [hc.eventually hlocal] with x hx
    rw [hRs, ← hseg u, ← hseg v, mem_union, hmem, hmem, hmem]
    exact hx
  have hcount := R.ncard_neighborSet_eq_two_of_local_segments_zero hR hRbound hzero
    (sub_ne_zero.mpr hu) (sub_ne_zero.mpr hv) hinter' hlocalR
  rw [R.ncard_edgeGraph_neighborSet] at hcount
  have hlink := hf.ncard_embeddedImage_faceLink hAi.injOn hp
  simp only [Finset.image_singleton] at hlink
  rw [hAp] at hlink
  rw [K.ncard_edgeGraph_neighborSet]
  exact hlink.symm.trans hcount

end Geometry.SimplicialComplex
