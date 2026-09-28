import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.EdgeIntervalMatching
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.EdgeFaceIncidence









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem original_edges_eq_of_nonvertex_contact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) {a b : Finset E}
    (ha : a ∈ K.faces) (hb : b ∈ K.faces) (ha2 : a.card = 2) (hb2 : b.card = 2)
    {x : E} (hxa : x ∈ convexHull ℝ (a : Set E)) (hxb : x ∈ convexHull ℝ (b : Set E))
    (hxv : x ∉ (a : Set E)) : a = b := by
  by_contra hne
  have hproper : a ∩ b ⊂ a := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left,by
    intro he
    have hab : a ⊆ b := he ▸ Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hab (by omega))⟩
  have hlt := Finset.card_lt_card hproper
  have hx : x ∈ convexHull ℝ ((a ∩ b : Finset E) : Set E) := by
    rw [Finset.coe_inter,←K.convexHull_inter_convexHull ha hb]
    exact ⟨hxa,hxb⟩
  have hne0 : (a ∩ b).card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero.mp h0,Finset.coe_empty,convexHull_empty] at hx
    exact hx
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show (a ∩ b).card = 1 by omega)
  have hxv' : x = v := by
    simpa only [hv,Finset.coe_singleton,convexHull_singleton,mem_singleton_iff] using hx
  apply hxv
  rw [hxv']
  exact Finset.inter_subset_left (hv.symm ▸ Finset.mem_singleton_self v)

theorem affine_unit_interval_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (e : ℝ →ᴬ[ℝ] E) :
    e '' Icc (0 : ℝ) 1 = convexHull ℝ ({e 0,e 1} : Set E) := by
  rw [convexHull_pair,←segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
  have h := image_segment ℝ e.toAffineMap (0 : ℝ) (1 : ℝ)
  exact h



theorem original_simplicial_edge_gaps_match
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (e f : ℝ →ᴬ[ℝ] E)
    (he : Function.Injective e) (hf : Function.Injective f)
    (heK : ({e 0,e 1} : Finset E) ∈ K.faces)
    (hfK : ({f 0,f 1} : Finset E) ∈ K.faces)
    {T : Set E} {a b c d : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hd1 : d ≤ 1)
    (ha : e a ∈ T) (hb : e b ∈ T) (hc : f c ∈ T) (hd : f d ∈ T)
    (hab : Disjoint (e '' Ioo a b) T) (hcd : Disjoint (f '' Ioo c d) T)
    (hmeet : ((e '' Ioo a b) ∩ (f '' Ioo c d)).Nonempty) :
    ({e 0,e 1} : Finset E) = {f 0,f 1} ∧ e '' Icc a b = f '' Icc c d := by
  obtain ⟨x,⟨t,ht,htx⟩,u,hu,hux⟩ := hmeet
  have he01 : e 0 ≠ e 1 := fun h => zero_ne_one (he h)
  have hf01 : f 0 ≠ f 1 := fun h => zero_ne_one (hf h)
  have ht01 : t ∈ Ioo (0 : ℝ) 1 := ⟨ha0.trans_lt ht.1,ht.2.trans_le hb1⟩
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hc0.trans_lt hu.1,hu.2.trans_le hd1⟩
  have hxe : x ∈ convexHull ℝ ({e 0,e 1} : Set E) :=
    (affine_unit_interval_image e).subset ⟨t,⟨ht01.1.le,ht01.2.le⟩,htx⟩
  have hxf : x ∈ convexHull ℝ ({f 0,f 1} : Set E) :=
    (affine_unit_interval_image f).subset ⟨u,⟨hu01.1.le,hu01.2.le⟩,hux⟩
  have hxv : x ∉ ({e 0,e 1} : Set E) := by
    rintro (hx | hx)
    · exact ht01.1.ne' (he (htx.trans hx))
    · exact ht01.2.ne (he (htx.trans (mem_singleton_iff.mp hx)))
  have hedge := original_edges_eq_of_nonvertex_contact K heK hfK
    (by simp [he01]) (by simp [hf01])
    (by simpa only [Finset.coe_insert,Finset.coe_singleton] using hxe)
    (by simpa only [Finset.coe_insert,Finset.coe_singleton] using hxf)
    (by simpa only [Finset.coe_insert,Finset.coe_singleton] using hxv)
  refine ⟨hedge,affine_edge_cut_intervals_eq e f he ?_ ha hb hc hd hab hcd ?_⟩
  · simpa only [Finset.coe_insert,Finset.coe_singleton] using congrArg (fun s : Finset E => (s : Set E)) hedge
  · exact ⟨x,⟨t,ht,htx⟩,u,hu,hux⟩

end PoincareConjecture.M76.PrismBelt
