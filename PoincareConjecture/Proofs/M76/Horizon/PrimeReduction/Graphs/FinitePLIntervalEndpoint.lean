import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

theorem ncard_neighborSet_eq_one_of_local_segment_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p u : E} (hp : p ∈ K.vertices) (hu : u ≠ p)
    (hlocal : ∀ᶠ x in 𝓝 p, x ∈ K.space ↔ x ∈ segment ℝ p u) :
    (K.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hp⟩).ncard = 1 := by
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
    change {0} ∈ R.faces
    have h := (hf.image_mem_embeddedImage_iff hAi.injOn (K.subset_space hp)).mpr hp
    simpa only [Finset.image_singleton, hAp] using h
  have hRs : R.space = (fun x => x - p) '' K.space := hf.embeddedImage_space hAi.injOn
  have hmem (T : Set E) (x : E) : x ∈ (fun t => t - p) '' T ↔ x + p ∈ T := by
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa only [sub_add_cancel] using ht
    · intro hx
      exact ⟨x + p, hx, add_sub_cancel_right x p⟩
  have hseg : (fun x => x - p) '' segment ℝ p u = segment ℝ 0 (u - p) := by
    have h := image_segment ℝ A.toAffineMap p u
    change (fun x => x - p) '' segment ℝ p u = segment ℝ (p - p) (u - p) at h
    simpa only [sub_self] using h
  have hc : Tendsto (fun x : E => x + p) (𝓝 0) (𝓝 p) := by
    have hc' : Continuous (fun x : E => x + p) := continuous_id.add continuous_const
    simpa only [zero_add] using hc'.tendsto (0 : E)
  have hlocalR : ∀ᶠ x in 𝓝 (0 : E), x ∈ R.space ↔ x ∈ segment ℝ 0 (u - p) := by
    filter_upwards [hc.eventually hlocal] with x hx
    rw [hRs, ← hseg, hmem, hmem]
    exact hx
  have hcount := R.ncard_neighborSet_eq_one_of_local_segment hR hzero
    (sub_ne_zero.mpr hu) hlocalR
  rw [R.ncard_edgeGraph_neighborSet] at hcount
  have hlink := hf.ncard_embeddedImage_faceLink hAi.injOn hp
  simp only [Finset.image_singleton] at hlink
  rw [hAp] at hlink
  rw [K.ncard_edgeGraph_neighborSet]
  exact hlink.symm.trans hcount

theorem exists_segment_germ_of_link_vertices_ncard_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) (hcount : (K.faceLink {p}).vertices.ncard = 1) :
    ∃ u : E, u ≠ p ∧ ∀ᶠ x in 𝓝 p, x ∈ K.space ↔ x ∈ segment ℝ p u := by
  obtain ⟨u, hset⟩ := ncard_eq_one.mp hcount
  have hu : u ∈ (K.faceLink {p}).vertices := hset.symm ▸ mem_singleton u
  have hpu : p ≠ u := by simpa using hu.2.1
  have huf : ({p, u} : Finset E) ∈ K.faces := by
    simpa only [Finset.union_singleton, Finset.pair_comm] using hu.2.2
  have huK : segment ℝ p u ⊆ K.space := by
    simpa only [Finset.coe_pair, convexHull_pair] using K.convexHull_subset_space huf
  refine ⟨u, hpu.symm, ?_⟩
  obtain ⟨r, hr, hstar⟩ := K.exists_ball_inter_space_subset_closedStar hK hp
  filter_upwards [Metric.ball_mem_nhds p hr] with x hxball
  refine ⟨?_, fun hx => huK hx⟩
  intro hx
  obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp (hstar ⟨hx, hxball⟩)
  have hsub : (a : Set E) ⊆ {p, u} := by
    intro w hw
    by_cases hwp : w = p
    · exact Or.inl hwp
    · have hwface : ({p, w} : Finset E) ∈ K.faces :=
        K.down_closed ha.2 (by simp only [Finset.insert_subset_iff, Finset.mem_insert,
          true_or, Finset.singleton_subset_iff]; exact ⟨trivial, Or.inr hw⟩)
          (Finset.insert_nonempty _ _)
      have hwlink : w ∈ (K.faceLink {p}).vertices :=
        ⟨K.down_closed ha.1 (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _),
          by simpa using (Ne.symm hwp),
          by simpa only [Finset.union_singleton, Finset.pair_comm] using hwface⟩
      exact Or.inr (hset.subset hwlink)
  simpa only [convexHull_pair] using convexHull_mono hsub hxa

end Geometry.SimplicialComplex

namespace Set

open Geometry

theorem IsFinitePLBallPair.exists_segment_germ_of_mem_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d rim : Set E} (hd : IsFinitePLBallPair ℝ d rim) {p : E} (hp : p ∈ rim) :
    ∃ u : E, u ≠ p ∧ ∀ᶠ x in 𝓝 p, x ∈ d ↔ x ∈ segment ℝ p u := by
  classical
  obtain ⟨hrim, C, hC, hcv, hne, e, he, hboundary⟩ := hd
  obtain ⟨f, ⟨K, hK, hKs, hfK⟩, hef⟩ := he.symm
  let z : ℝ := e ⟨p, hrim hp⟩
  have hzC : z ∈ C := (e ⟨p, hrim hp⟩).property
  have hzfront : z ∈ frontier C := (hboundary ⟨p, hrim hp⟩).mp hp
  have hCI : C = Icc (sInf C) (sSup C) :=
    eq_Icc_of_connected_compact (hcv.isConnected (hne.mono interior_subset)) hC
  have hlt : sInf C < sSup C := by
    rw [hCI, interior_Icc] at hne
    exact nonempty_Ioo.mp hne
  have hfront : frontier C = {sInf C, sSup C} :=
    (congrArg frontier hCI).trans (frontier_Icc hlt.le)
  have hsegment : ∃ u : ℝ, u ≠ z ∧ C = segment ℝ z u := by
    rw [hfront] at hzfront
    rcases hzfront with hz | hz
    · exact ⟨sSup C, hz ▸ hlt.ne', by rw [hz, segment_eq_Icc hlt.le]; exact hCI⟩
    · exact ⟨sInf C, hz ▸ hlt.ne,
        by rw [hz, segment_symm, segment_eq_Icc hlt.le]; exact hCI⟩
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
  have hcountR : (R.faceLink {z}).vertices.ncard = 1 := by
    obtain ⟨u, hu, hCu⟩ := hsegment
    have hh := R.ncard_neighborSet_eq_one_of_local_segment_at hR hzv hu
      (Filter.Eventually.of_forall (fun x => by rw [hRs, hCu]))
    rwa [R.ncard_edgeGraph_neighborSet] at hh
  have hcountM : (M.faceLink {p}).vertices.ncard = 1 := by
    have hh := hfR.ncard_embeddedImage_faceLink hfiR hzv
    simpa only [Finset.image_singleton, hfz] using hh.trans hcountR
  obtain ⟨u, hu, hlocal⟩ := M.exists_segment_germ_of_link_vertices_ncard_one hM hpM hcountM
  exact ⟨u, hu, by simpa only [hMs] using hlocal⟩

end Set
