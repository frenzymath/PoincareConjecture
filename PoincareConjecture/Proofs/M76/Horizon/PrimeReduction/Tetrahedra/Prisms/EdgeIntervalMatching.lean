import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleContacts

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem cut_gap_endpoints_eq
    {T : Set ℝ} {a b c d x : ℝ}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (hab : Disjoint (Ioo a b) T) (hcd : Disjoint (Ioo c d) T)
    (hx : x ∈ Ioo a b ∩ Ioo c d) : a = c ∧ b = d := by
  have hac : a ≤ c := by
    by_contra h
    exact disjoint_left.mp hcd ⟨lt_of_not_ge h, hx.1.1.trans hx.2.2⟩ ha
  have hca : c ≤ a := by
    by_contra h
    exact disjoint_left.mp hab ⟨lt_of_not_ge h, hx.2.1.trans hx.1.2⟩ hc
  have hbd : b ≤ d := by
    by_contra h
    exact disjoint_left.mp hab ⟨hx.1.1.trans hx.2.2, lt_of_not_ge h⟩ hd
  have hdb : d ≤ b := by
    by_contra h
    exact disjoint_left.mp hcd ⟨hx.2.1.trans hx.1.2, lt_of_not_ge h⟩ hb
  exact ⟨le_antisymm hac hca,le_antisymm hbd hdb⟩

theorem parameterized_cut_gap_eq
    {E : Type*} (e : ℝ → E) (he : Function.Injective e) {T : Set E}
    {a b c d : ℝ} (ha : e a ∈ T) (hb : e b ∈ T) (hc : e c ∈ T) (hd : e d ∈ T)
    (hab : Disjoint (e '' Ioo a b) T) (hcd : Disjoint (e '' Ioo c d) T)
    (hmeet : ((e '' Ioo a b) ∩ (e '' Ioo c d)).Nonempty) :
    e '' Icc a b = e '' Icc c d := by
  obtain ⟨y,⟨x,hx,rfl⟩,z,hz,hzx⟩ := hmeet
  have hzx' := he hzx
  subst z
  have h₁ : Disjoint (Ioo a b) (e ⁻¹' T) := disjoint_left.mpr
    (fun t ht hT => disjoint_left.mp hab (mem_image_of_mem e ht) hT)
  have h₂ : Disjoint (Ioo c d) (e ⁻¹' T) := disjoint_left.mpr
    (fun t ht hT => disjoint_left.mp hcd (mem_image_of_mem e ht) hT)
  obtain ⟨rfl,rfl⟩ := cut_gap_endpoints_eq ha hb hc hd h₁ h₂ ⟨hx,hz⟩
  rfl

private theorem affine_edge_orientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e f : ℝ →ᴬ[ℝ] E) (hends : ({e 0,e 1} : Set E) = {f 0,f 1}) :
    (∀ t, f t = e t) ∨ (∀ t, f t = e (1-t)) := by
  have hparam (g : ℝ →ᴬ[ℝ] E) (t : ℝ) :
      g t = AffineMap.lineMap (g 0) (g 1) t := by
    have h := g.toAffineMap.apply_lineMap (0 : ℝ) (1 : ℝ) t
    simp only [AffineMap.lineMap_apply_ring,sub_zero,mul_one,mul_zero,zero_add] at h
    exact h
  rcases pair_eq_pair_iff.mp hends with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl (fun t => by rw [hparam f,hparam e,h0,h1])
  · exact Or.inr (fun t => by rw [hparam f,hparam e,AffineMap.lineMap_apply_one_sub,h0,h1])

private theorem reversed_image_Icc {E : Type*} (e : ℝ → E) (c d : ℝ) :
    (fun t => e (1-t)) '' Icc c d = e '' Icc (1-d) (1-c) := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,by simp⟩

private theorem reversed_image_Ioo {E : Type*} (e : ℝ → E) (c d : ℝ) :
    (fun t => e (1-t)) '' Ioo c d = e '' Ioo (1-d) (1-c) := by
  ext y
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    exact ⟨1-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,by simp⟩

theorem affine_edge_cut_intervals_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e f : ℝ →ᴬ[ℝ] E) (he : Function.Injective e)
    (hends : ({e 0,e 1} : Set E) = {f 0,f 1}) {T : Set E} {a b c d : ℝ}
    (ha : e a ∈ T) (hb : e b ∈ T) (hc : f c ∈ T) (hd : f d ∈ T)
    (hab : Disjoint (e '' Ioo a b) T) (hcd : Disjoint (f '' Ioo c d) T)
    (hmeet : ((e '' Ioo a b) ∩ (f '' Ioo c d)).Nonempty) :
    e '' Icc a b = f '' Icc c d := by
  rcases affine_edge_orientation e f hends with hf | hf
  · have hfun : (f : ℝ → E) = e := funext hf
    rw [hfun] at hc hd hcd hmeet ⊢
    exact parameterized_cut_gap_eq e he ha hb hc hd hab hcd hmeet
  · have hfun : (f : ℝ → E) = fun t => e (1-t) := funext hf
    rw [hfun,reversed_image_Ioo] at hcd hmeet
    rw [hfun,reversed_image_Icc]
    exact parameterized_cut_gap_eq e he ha hb (hf d ▸ hd) (hf c ▸ hc) hab hcd hmeet

end PoincareConjecture.M76.PrismBelt
