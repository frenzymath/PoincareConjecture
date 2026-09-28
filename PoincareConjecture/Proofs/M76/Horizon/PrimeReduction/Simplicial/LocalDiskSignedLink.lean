import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskLinkPolygon
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.Mathlib.PolygonStrictSigns
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSignPerturbation
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem ncard_link_affine_zero_of_local_segments
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p u v : E} (hp : p ∈ K.vertices) (A : E →ᵃ[ℝ] ℝ)
    (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ K.space ∩ {y | A y = 0} ↔ x ∈ segment ℝ p u ∪ segment ℝ p v) :
    ((K.link p).space ∩ {x | A x = 0}).ncard = 2 := by
  have hpA : A p = 0 :=
    ((mem_of_mem_nhds hlocal).mpr (Or.inl (left_mem_segment ℝ p u))).2
  let e : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  have hep : e p = 0 := by change -p + p = 0; exact neg_add_cancel p
  have hheight (x : E) : A.linear (e x) = A x := by
    change A.linear (-p + x) = A x
    have h : A.linear (-p + x) = A x - A p := by
      simpa only [vsub_eq_sub, sub_eq_add_neg, add_comm] using A.linearMap_vsub x p
    simpa only [hpA, sub_zero] using h
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let R := hf.embeddedImage e.injective.injOn
  have hR : R.faces.Finite := hf.embeddedImage_finite e.injective.injOn hK
  have hRs : R.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have hRzero : (0 : E) ∈ R.vertices := by
    rw [hf.embeddedImage_vertices e.injective.injOn]
    exact ⟨p, hp, hep⟩
  have hRlink : (R.link 0).space = e '' (K.link p).space := by
    have h := hf.embeddedImage_link_space e.injective.injOn hp
    change (R.link (e p)).space = e '' (K.link p).space at h
    simpa only [hep] using h
  have hseg (w : E) : e '' segment ℝ p w = segment ℝ 0 (e w) := by
    have h := image_segment ℝ e.toAffineEquiv.toAffineMap p w
    change e '' segment ℝ p w = segment ℝ (e p) (e w) at h
    simpa only [hep] using h
  have hinterR : segment ℝ 0 (e u) ∩ segment ℝ 0 (e v) ⊆ {0} := by
    intro x hx
    have hu' : e.symm x ∈ segment ℝ p u := by
      obtain ⟨z, hz, hzx⟩ := (hseg u).symm.subset hx.1
      simpa only [← hzx, e.symm_apply_apply] using hz
    have hv' : e.symm x ∈ segment ℝ p v := by
      obtain ⟨z, hz, hzx⟩ := (hseg v).symm.subset hx.2
      simpa only [← hzx, e.symm_apply_apply] using hz
    have hxp : e.symm x = p := hinter ⟨hu', hv'⟩
    have h := congrArg e hxp
    simpa only [e.apply_symm_apply, hep, mem_singleton_iff] using h
  have hmem (S : Set E) (x : E) : x ∈ e '' S ↔ e.symm x ∈ S := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [e.symm_apply_apply] using hz
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hcont : Tendsto e.symm (𝓝 0) (𝓝 p) := by
    have h := e.symm.continuous.tendsto (0 : E)
    have hzero : e.symm 0 = p := by rw [← hep, e.symm_apply_apply]
    simpa only [hzero] using h
  have hlocalR : ∀ᶠ x in 𝓝 (0 : E),
      x ∈ R.space ∩ {y | A.linear y = 0} ↔
        x ∈ segment ℝ 0 (e u) ∪ segment ℝ 0 (e v) := by
    filter_upwards [hcont.eventually hlocal] with x hx
    have hh : A.linear x = A (e.symm x) := by
      simpa only [e.apply_symm_apply] using hheight (e.symm x)
    rw [hRs, ← hseg u, ← hseg v, mem_union, hmem, hmem,
      mem_inter_iff, hmem, mem_ofPred_eq, hh]
    exact hx
  have hcount := R.ncard_link_zero_of_local_segments hR hRzero A.linear
    (fun h => hu (e.injective (h.trans hep.symm)))
    (fun h => hv (e.injective (h.trans hep.symm))) hinterR hlocalR
  have hsection : (R.link 0).space ∩ {x | A.linear x = 0} =
      e '' ((K.link p).space ∩ {x | A x = 0}) := by
    rw [hRlink]
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzA⟩
      change A.linear (e z) = 0 at hzA
      exact ⟨z, ⟨hz, (hheight z).symm.trans hzA⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzA⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      change A.linear (e z) = 0
      rw [hheight]
      exact hzA
  rw [hsection, Set.ncard_image_of_injective _ e.injective] at hcount
  exact hcount

omit [FiniteDimensional ℝ E] in

theorem exists_positive_link_vertex_of_affine_surface_accumulation
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ K.vertices) (A : E →ᵃ[ℝ] ℝ) (hpA : A p = 0)
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ v ∈ (K.link p).vertices, 0 < A v := by
  obtain ⟨v, hpv, hvA⟩ :=
    K.exists_positive_graph_neighbor_of_mem_closure hK A ⟨p, hp⟩ hpA hpos
  have hpv' : p ≠ (v : E) := fun h => hpv.1 (Subtype.ext h)
  have hface : ({p, (v : E)} : Finset E) ∈ K.faces := by
    have h := hpv.2
    change ({(⟨p, hp⟩ : K.vertices), v} : Finset K.vertices).map
      (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
  exact ⟨v, ⟨v.property, by simpa only [Finset.mem_singleton] using hpv', hface⟩, hvA⟩

omit [FiniteDimensional ℝ E] in

theorem exists_nonzero_vertex_of_finite_affine_zero_section
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (hfinite : (K.space ∩ {x | A x = 0}).Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2) :
    ∃ v ∈ s, A v ≠ 0 := by
  by_contra! hz
  have hsub : convexHull ℝ (s : Set E) ⊆ K.space ∩ {x | A x = 0} := by
    intro x hx
    refine ⟨K.convexHull_subset_space hs hx, ?_⟩
    exact convexHull_min (fun v hv => hz v hv) ((convex_singleton (0 : ℝ)).affine_preimage A) hx
  have hsingle : (convexHull ℝ (s : Set E)).Subsingleton :=
    (convex_convexHull ℝ _).isPreconnected.isDiscrete_iff_subsingleton.mp
      (hfinite.subset hsub).isDiscrete
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hs2
  exact huv (hsingle (subset_convexHull ℝ _ (by simp))
    (subset_convexHull ℝ _ (by simp)))

theorem exists_signed_link_polygon_of_local_disk_and_section
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    {p u v : E} (hp : p ∈ K.vertices) {d rim : Set E}
    (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim) (hdK : d ⊆ K.space)
    (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : E →ᵃ[ℝ] ℝ) (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ K.space ∩ {y | A y = 0} ↔ x ∈ segment ℝ p u ∪ segment ℝ p v)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ (n : ℕ) (Q : Polygon E (n + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (K.link p).space ∧
      ((K.link p).space ∩ {x | A x = 0}).ncard = 2 ∧
      IsConnected ((K.link p).space ∩ {x | A x < 0}) ∧
      IsConnected ((K.link p).space ∩ {x | 0 < A x}) ∧
      (∀ x ∈ (K.link p).space, A x = 0 →
        x ∈ closure ((K.link p).space ∩ {y | A y < 0}) ∧
          x ∈ closure ((K.link p).space ∩ {y | 0 < A y})) ∧
      (∀ s ∈ (K.link p).faces, s.card = 2 → ∃ v ∈ s, A v ≠ 0) ∧
      (∃ v ∈ (K.link p).vertices, A v < 0) ∧
      (∃ v ∈ (K.link p).vertices, 0 < A v) := by
  obtain ⟨n, Q, hQi, hQ, hQs⟩ :=
    K.exists_link_polygon_of_local_finitePLDisk hK hbound hp hd hdK hpd hopen
  have hpA : A p = 0 :=
    ((mem_of_mem_nhds hlocal).mpr (Or.inl (left_mem_segment ℝ p u))).2
  have hcount := K.ncard_link_affine_zero_of_local_segments hK hp A hu hv hinter hlocal
  have hpv := K.exists_positive_link_vertex_of_affine_surface_accumulation hK hp A hpA hpos
  have hnv : ∃ v ∈ (K.link p).vertices, A v < 0 := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      K.exists_positive_link_vertex_of_affine_surface_accumulation hK hp (-A)
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hpA)
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg)
  have hnb : ∃ x ∈ Q.boundary ℝ, A x < 0 := by
    obtain ⟨x, hx, hxA⟩ := hnv
    exact ⟨x, hQs.symm.subset ((K.link p).vertices_subset_space hx), hxA⟩
  have hpb : ∃ x ∈ Q.boundary ℝ, 0 < A x := by
    obtain ⟨x, hx, hxA⟩ := hpv
    exact ⟨x, hQs.symm.subset ((K.link p).vertices_subset_space hx), hxA⟩
  obtain ⟨hn, hpos', hz⟩ := Q.strict_sign_data hQ hQi A
    A.continuous_of_finiteDimensional.continuousOn (by simpa only [hQs] using hcount) hnb hpb
  rw [hQs] at hn hpos' hz
  refine ⟨n, Q, hQi, hQ, hQs, hcount, hn, hpos', hz, ?_, hnv, hpv⟩
  intro s hs hs2
  exact (K.link p).exists_nonzero_vertex_of_finite_affine_zero_section A
    (Set.finite_of_ncard_ne_zero (by rw [hcount]; norm_num)) hs hs2

end Geometry.SimplicialComplex
