import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.TwoSegmentGermDegree
import PoincareConjecture.Proofs.M76.Mathlib.PrescribedSubdivisionVertices
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]



theorem exists_two_segment_germ_of_link_vertices_ncard
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ a ∈ K.faces, a.card ≤ 2) {p : E} (hp : p ∈ K.vertices)
    (hcount : (K.faceLink {p}).vertices.ncard = 2) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      segment ℝ p u ∩ segment ℝ p v ⊆ {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ K.space ↔ x ∈ segment ℝ p u ∪ segment ℝ p v := by
  obtain ⟨u, v, huv, hset⟩ := ncard_eq_two.mp hcount
  have hu : u ∈ (K.faceLink {p}).vertices := hset.symm ▸ Or.inl rfl
  have hv : v ∈ (K.faceLink {p}).vertices := hset.symm ▸ Or.inr rfl
  have hpu : p ≠ u := by simpa using hu.2.1
  have hpv : p ≠ v := by simpa using hv.2.1
  have huf : ({p, u} : Finset E) ∈ K.faces := by
    simpa only [Finset.union_singleton, Finset.pair_comm] using hu.2.2
  have hvf : ({p, v} : Finset E) ∈ K.faces := by
    simpa only [Finset.union_singleton, Finset.pair_comm] using hv.2.2
  have huK : segment ℝ p u ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space huf
  have hvK : segment ℝ p v ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space hvf
  refine ⟨u, v, hpu.symm, hpv.symm, ?_, ?_⟩
  · have heq : ({p, u} : Set E) ∩ {p, v} = {p} := by
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      aesop
    have h := K.inter_subset_convexHull huf hvf
    simpa only [Finset.coe_pair, convexHull_pair, heq, convexHull_singleton] using h
  · obtain ⟨r, hr, hstar⟩ := K.exists_ball_inter_space_subset_closedStar hK hp
    filter_upwards [Metric.ball_mem_nhds p hr] with x hxball
    constructor
    · intro hx
      by_cases hxp : x = p
      · exact Or.inl (hxp.symm ▸ left_mem_segment ℝ p u)
      obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp (hstar ⟨hx, hxball⟩)
      have hle := hbound (insert p a) ha.2
      have hne : (insert p a).Nonempty := Finset.insert_nonempty _ _
      have hc : (insert p a).card = 2 := by
        have hpos := Finset.card_pos.mpr hne
        have hnot : (insert p a).card ≠ 1 := by
          intro hc
          obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
          have hpz : p = z := by simpa only [hz, Finset.mem_singleton] using
            (Finset.mem_insert_self p a)
          apply hxp
          have hh := convexHull_mono (Finset.subset_insert p a) hxa
          simpa only [hz, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff,
            ← hpz] using hh
        omega
      obtain ⟨w, hw, hwa⟩ := Finset.exists_eq_insert_iff.mpr
        ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self p a), by simp [hc]⟩
      have hwp : w ≠ p := by simpa using hw
      have hwface : ({p, w} : Finset E) ∈ K.faces := by
        simpa only [← hwa, Finset.pair_comm] using ha.2
      have hwlink : w ∈ (K.faceLink {p}).vertices :=
        ⟨K.down_closed hwface (by simp) (Finset.singleton_nonempty w),
          by simpa using hwp.symm,
          by simpa only [Finset.union_singleton, Finset.pair_comm] using hwface⟩
      have hxseg : x ∈ segment ℝ p w := by
        have hh := convexHull_mono (Finset.subset_insert p a) hxa
        simpa only [← hwa, Finset.coe_pair, convexHull_pair, segment_symm] using hh
      rcases hset.subset hwlink with rfl | rfl
      · exact Or.inl hxseg
      · exact Or.inr hxseg
    · exact fun hx => hx.elim (fun h => huK h) (fun h => hvK h)

end Geometry.SimplicialComplex

namespace Set

open Geometry



theorem IsFinitePLBallPair.exists_two_segment_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d rim : Set E} (hd : IsFinitePLBallPair ℝ d rim) {p : E} (hp : p ∈ d \ rim) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      segment ℝ p u ∩ segment ℝ p v ⊆ {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ d ↔ x ∈ segment ℝ p u ∪ segment ℝ p v := by
  classical
  obtain ⟨_, C, _, _, _, e, he, hboundary⟩ := hd
  obtain ⟨f, ⟨K, hK, hKs, hfK⟩, hef⟩ := he.symm
  let z : ℝ := e ⟨p, hp.1⟩
  have hzC : z ∈ C := (e ⟨p, hp.1⟩).property
  have hzint : z ∈ interior C := by
    by_contra hn
    exact hp.2 ((hboundary ⟨p, hp.1⟩).mpr ⟨subset_closure hzC, hn⟩)
  have hfz : f z = p := by rw [← hef, e.symm_apply_apply]
  have hfi : InjOn f C := by
    intro x hx y hy hxy
    rw [← hef ⟨x, hx⟩, ← hef ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (e.symm.injective (Subtype.ext hxy))
  have hfs : f '' C = d := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e.symm ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).property, by rw [← hef, e.symm_apply_apply]⟩
  obtain ⟨R, hR, hRK, hzR⟩ := K.exists_finite_subdivision_with_vertices hK {z}
    (by simpa only [Finset.coe_singleton, singleton_subset_iff, hKs] using hzC)
  have hRs : R.space = C := hRK.space_eq.trans hKs
  have hzv : z ∈ R.vertices := hzR (by simp)
  have hfR : R.AffineOnFaces f := hRK.affineOnFaces hfK
  have hfiR : InjOn f R.space := hRs ▸ hfi
  let M := hfR.embeddedImage hfiR
  have hM : M.faces.Finite := hfR.embeddedImage_finite hfiR hR
  have hMs : M.space = d := by rw [hfR.embeddedImage_space hfiR, hRs, hfs]
  have hpM : p ∈ M.vertices := by
    change {p} ∈ M.faces
    have hh := (hfR.image_mem_embeddedImage_iff hfiR (R.subset_space hzv)).mpr hzv
    simpa only [Finset.image_singleton, hfz] using hh
  have hbound : ∀ a ∈ M.faces, a.card ≤ 2 := by
    intro a ha
    rw [hfR.embeddedImage_faces hfiR] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hh := (R.indep hb).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    exact Finset.card_image_le.trans (by simpa using hh)
  have hcountR : (R.faceLink {z}).vertices.ncard = 2 :=
    R.faceLink_ncard_eq_two_of_hull_meets_interior hR hzv (by simp)
      ⟨z, by simp, by simpa only [hRs] using hzint⟩
  have hcountM : (M.faceLink {p}).vertices.ncard = 2 := by
    have hh := hfR.ncard_embeddedImage_faceLink hfiR hzv
    simpa only [Finset.image_singleton, hfz] using hh.trans hcountR
  obtain ⟨u, v, hu, hv, hinter, hlocal⟩ :=
    M.exists_two_segment_germ_of_link_vertices_ncard hM hbound hpM hcountM
  exact ⟨u, v, hu, hv, hinter, by simpa only [hMs] using hlocal⟩

end Set
