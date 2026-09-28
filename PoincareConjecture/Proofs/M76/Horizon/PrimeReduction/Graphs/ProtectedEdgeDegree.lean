import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskEdgeCofaces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.TwoSegmentGermDegree
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier










set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]



theorem convexHull_insert_zero_base_inter_zero
    (A : E →ᵃ[ℝ] ℝ) (s : Finset E) {a : E}
    (hs : ∀ v ∈ s, A v = 0) (ha : A a ≠ 0) :
    convexHull ℝ ((insert a s : Finset E) : Set E) ∩ {x | A x = 0} =
      convexHull ℝ (s : Set E) := by
  classical
  have hapos (B : E →ᵃ[ℝ] ℝ) (hB : ∀ v ∈ s, B v = 0) (haB : 0 < B a)
      {x : E} (hx : x ∈ convexHull ℝ ((insert a s : Finset E) : Set E))
      (hxB : B x = 0) : x ∈ convexHull ℝ (s : Set E) := by
    have hn (v : E) (hv : v ∈ insert a s) : 0 ≤ B v := by
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact haB.le
      · rw [hB v hv]
    have h := (insert a s).mem_convexHull_zero_vertices B hn hx hxB
    apply convexHull_mono (s := ((insert a s : Finset E) : Set E) ∩ {v | B v = 0}) _ h
    rintro v ⟨hv, hvB⟩
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact False.elim (haB.ne' hvB)
    · exact hv
  apply Subset.antisymm
  · rintro x ⟨hx, hxA⟩
    change A x = 0 at hxA
    rcases lt_or_gt_of_ne ha with han | hap
    · exact hapos (-A) (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hs)
        (neg_pos.mpr han) hx (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hxA)
    · exact hapos A hs hap hx hxA
  · intro x hx
    exact ⟨convexHull_mono (Finset.subset_insert a s) hx,
      convexHull_min hs ((convex_singleton (0 : ℝ)).affine_preimage A) hx⟩

end AffineMap

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_signed_edge_cofaces_of_local_disk
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3) {s : Finset E}
    (hs : s ∈ K.faces) (hs2 : s.card = 2) {p : E}
    (hps : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {d rim : Set E} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : E →ᵃ[ℝ] ℝ) (hsA : ∀ v ∈ s, A v = 0)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x})) :
    ∃ a b : E, a ∉ s ∧ b ∉ s ∧ insert a s ∈ K.faces ∧ insert b s ∈ K.faces ∧
      A a < 0 ∧ 0 < A b ∧
      ∀ᶠ x in 𝓝 p, x ∈ K.space ↔
        x ∈ convexHull ℝ ((insert a s : Finset E) : Set E) ∪
          convexHull ℝ ((insert b s : Finset E) : Set E) := by
  obtain ⟨t, r, htr, hset⟩ := ncard_eq_two.mp
    (K.ncard_triangle_cofaces_eq_two_of_local_disk hK hbound hs hs2 hps hd hdK hpd hopen)
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t :=
    hset.symm.subset (Or.inl rfl)
  have hr : r ∈ K.faces ∧ r.card = 3 ∧ s ⊆ r :=
    hset.symm.subset (Or.inr rfl)
  have hexhaust (z : Finset E) (hz : z ∈ K.faces) (hsz : s ⊆ z) : z ⊆ t ∨ z ⊆ r := by
    have hlo := Finset.card_le_card hsz
    have hhi := hbound z hz
    by_cases hz2 : z.card = 2
    · have he : s = z := Finset.eq_of_subset_of_card_le hsz (by omega)
      exact Or.inl (he ▸ ht.2.2)
    · have hm : z ∈ {z | z ∈ K.faces ∧ z.card = 3 ∧ s ⊆ z} := ⟨hz, by omega, hsz⟩
      rw [hset] at hm
      exact hm.elim (fun h => Or.inl (h ▸ Finset.Subset.rfl))
        (fun h => Or.inr (h ▸ Finset.Subset.rfl))
  obtain ⟨U, hU, hpU, hlocal⟩ := K.exists_open_two_coface_carrier_germ
    hK hs ht.1 hr.1 hexhaust hps
  obtain ⟨a, has, hat⟩ := Finset.exists_eq_insert_iff.mpr ⟨ht.2.2, by omega⟩
  obtain ⟨b, hbs, hbr⟩ := Finset.exists_eq_insert_iff.mpr ⟨hr.2.2, by omega⟩
  have hstrict (B : E →ᵃ[ℝ] ℝ) (hBs : ∀ v ∈ s, B v = 0)
      (hBpos : p ∈ closure (K.space ∩ {x | 0 < B x})) : 0 < B a ∨ 0 < B b := by
    obtain ⟨x, hxU, hxK, hxB⟩ := mem_closure_iff.mp hBpos U hU hpU
    change 0 < B x at hxB
    by_contra! h
    have hnonpos (v : E) (hv : B v ≤ 0) :
        convexHull ℝ ((insert v s : Finset E) : Set E) ⊆ {y | B y ≤ 0} := by
      apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage B)
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hv
      · exact (hBs z hz).le
    have hx := (hlocal x hxU).mp hxK
    rw [← hat, ← hbr] at hx
    exact hxB.not_ge (hx.elim (fun hx => hnonpos a h.1 hx) (fun hx => hnonpos b h.2 hx))
  have hpositive := hstrict A hsA hpos
  have hnegative : A a < 0 ∨ A b < 0 := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using
      hstrict (-A) (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hsA)
        (by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] using hneg)
  have hlocal' : ∀ᶠ x in 𝓝 p, x ∈ K.space ↔
      x ∈ convexHull ℝ ((insert a s : Finset E) : Set E) ∪
        convexHull ℝ ((insert b s : Finset E) : Set E) := by
    filter_upwards [hU.mem_nhds hpU] with x hx
    simpa only [hat, hbr] using hlocal x hx
  rcases hnegative with ha | hb
  · exact ⟨a, b, has, hbs, hat.symm ▸ ht.1, hbr.symm ▸ hr.1, ha,
      hpositive.resolve_left (not_lt_of_ge ha.le), hlocal'⟩
  · refine ⟨b, a, hbs, has, hbr.symm ▸ hr.1, hat.symm ▸ ht.1, hb,
      hpositive.resolve_right (not_lt_of_ge hb.le), ?_⟩
    simpa only [union_comm] using hlocal'




theorem eventually_moved_section_eq_fixed_edge_of_local_disk
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3) {s : Finset E}
    (hs : s ∈ K.faces) (hs2 : s.card = 2) {p : E}
    (hps : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {d rim : Set E} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : E →ᵃ[ℝ] ℝ) (hsA : ∀ v ∈ s, A v = 0)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x}))
    (f : E ≃ₜ E) (hf : K.AffineOnFaces f)
    (hfix : EqOn f id (convexHull ℝ (s : Set E)))
    (hposv : ∀ w ∈ K.vertices, 0 < A w → 0 < A (f w))
    (hnegv : ∀ w ∈ K.vertices, A w < 0 → A (f w) < 0) :
    ∀ᶠ x in 𝓝 p, x ∈ f '' K.space ∩ {y | A y = 0} ↔
      x ∈ convexHull ℝ (s : Set E) := by
  obtain ⟨a, b, _, _, haK, hbK, haA, hbA, hlocal⟩ :=
    K.exists_signed_edge_cofaces_of_local_disk hK hbound hs hs2 hps hd hdK hpd hopen
      A hsA hneg hpos
  have hsection (v : E) (hvK : insert v s ∈ K.faces) (hvA : A (f v) ≠ 0)
      {x : E} (hx : x ∈ convexHull ℝ ((insert v s : Finset E) : Set E))
      (hxA : A (f x) = 0) : f x ∈ convexHull ℝ (s : Set E) := by
    obtain ⟨F, hF⟩ := hf (insert v s) hvK
    let C := A.comp F.toAffineMap
    have hCv : C v ≠ 0 := by
      change A (F v) ≠ 0
      rw [← hF (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))]
      exact hvA
    have hCs (w : E) (hw : w ∈ s) : C w = 0 := by
      change A (F w) = 0
      rw [← hF (subset_convexHull ℝ _ (Finset.mem_insert_of_mem hw)),
        hfix (subset_convexHull ℝ _ hw)]
      exact hsA w hw
    have hxC : C x = 0 := by change A (F x) = 0; rw [← hF hx]; exact hxA
    have hxbase := (C.convexHull_insert_zero_base_inter_zero s hCs hCv).subset ⟨hx, hxC⟩
    rw [hfix hxbase]
    exact hxbase
  have hpfix : f p = p := hfix (intrinsicInterior_subset hps)
  have hc : Tendsto f.symm (𝓝 p) (𝓝 p) := by
    have hpback : f.symm p = p := f.injective ((f.apply_symm_apply p).trans hpfix.symm)
    simpa only [hpback] using f.symm.continuous.tendsto p
  filter_upwards [hc.eventually hlocal] with x hx
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hyA⟩
    rw [f.symm_apply_apply] at hx
    rcases hx.mp hy with hya | hyb
    · exact hsection a haK (hnegv a (K.face_subset_vertices haK (by simp)) haA).ne hya hyA
    · exact hsection b hbK (hposv b (K.face_subset_vertices hbK (by simp)) hbA).ne' hyb hyA
  · intro hxbase
    refine ⟨⟨x, K.convexHull_subset_space hs hxbase, hfix hxbase⟩, ?_⟩
    exact convexHull_min hsA ((convex_singleton (0 : ℝ)).affine_preimage A) hxbase



theorem ncard_graph_degree_after_face_affine_motion_at_fixed_edge
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hG : G.faces.Finite) (hGbound : ∀ t ∈ G.faces, t.card ≤ 2)
    {s : Finset E} (hs : s ∈ K.faces) (hs2 : s.card = 2) {p : E}
    (hpG : p ∈ G.vertices)
    (hps : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {d rim : Set E} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdK : d ⊆ K.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen (Subtype.val ⁻¹' (d \ rim) : Set K.space))
    (A : E →ᵃ[ℝ] ℝ) (hsA : ∀ v ∈ s, A v = 0)
    (hneg : p ∈ closure (K.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (K.space ∩ {x | 0 < A x}))
    (f : E ≃ₜ E) (hf : K.AffineOnFaces f)
    (hfix : EqOn f id (convexHull ℝ (s : Set E)))
    (hposv : ∀ w ∈ K.vertices, 0 < A w → 0 < A (f w))
    (hnegv : ∀ w ∈ K.vertices, A w < 0 → A (f w) < 0)
    (hGlocal : ∀ᶠ x in 𝓝 p,
      x ∈ G.space ↔ x ∈ f '' K.space ∩ {y | A y = 0}) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨p, hpG⟩).ncard = 2 := by
  have hsection := K.eventually_moved_section_eq_fixed_edge_of_local_disk hK hbound hs hs2 hps
    hd hdK hpd hopen A hsA hneg hpos f hf hfix hposv hnegv
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs2
  have hpseg : p ∈ segment ℝ a b := by
    simpa only [Finset.coe_pair, convexHull_pair] using intrinsicInterior_subset hps
  have hpne (w : E) (hw : w ∈ ({a, b} : Finset E)) : w ≠ p := by
    intro h
    have hproper : ({w} : Finset E) ⊂ {a, b} := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.singleton_subset_iff.mpr hw, ?_⟩
      intro heq
      have hc := congrArg Finset.card heq
      simp only [Finset.card_singleton, Finset.card_pair hab] at hc
      omega
    have hfront := (K.indep hs).convexHull_subset_intrinsicFrontier hproper
      (show p ∈ convexHull ℝ (({w} : Finset E) : Set E) by simpa using h.symm)
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hfront
    exact hfront.2 hps
  have hbt : Wbtw ℝ a p b := mem_segment_iff_wbtw.mp hpseg
  have hsplit : segment ℝ p a ∪ segment ℝ p b = segment ℝ a b := by
    rw [segment_symm ℝ p a, hbt.segment_union]
  apply G.ncard_neighborSet_eq_two_of_local_segments hG hGbound hpG
    (hpne a (by simp)) (hpne b (by simp))
    (by rw [segment_symm ℝ p a, hbt.segment_inter_eq_endpoint])
  filter_upwards [hGlocal, hsection] with x hx hsx
  rw [hsplit]
  exact hx.trans (by simpa only [Finset.coe_pair, convexHull_pair] using hsx)

end Geometry.SimplicialComplex
