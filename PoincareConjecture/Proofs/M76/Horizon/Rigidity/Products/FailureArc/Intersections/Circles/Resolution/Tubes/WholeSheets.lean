import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SheetImages

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem SeparatedCircleSource.identity_whole_sheet_iff
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    {i : D.decomposition.Index} {L d : ℝ}
    (T : ComponentIdentityAnnuliData (e := e) (R := R) D.decomposition i L d)
    (hi : D.decomposition.pieces i = C₀)
    (hmi : D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁)
    (hwhole₀ : ∀ z ∈ T.tube '' _root_.Dehn.identityTube L d,
      z ∈ f₀ '' S₀ ↔ z ∈ f₀ '' D.first.space)
    (hwhole₁ : ∀ z ∈ T.tube '' _root_.Dehn.identityTube L d,
      z ∈ f₁ '' S₁ ↔ z ∈ f₁ '' D.second.space)
    (j : Fin 2) (z : P2 × ℝ) (hz : z ∈ _root_.Dehn.identityTube L d) :
    T.tube z ∈ (if T.label j = 0 then f₀ '' S₀ else f₁ '' S₁) ↔
      z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
  rw [← identity_tube_source_image_iff T j z hz]
  have hzimage : T.tube z ∈ T.tube '' _root_.Dehn.identityTube L d := ⟨z,hz,rfl⟩
  have hbranch := D.identity_source_subset T hi hmi
  have hloc (x : P2) (hx : x ∈ D.source.space) (hxz : D.map x = T.tube z) :
      ∃ k, x ∈ T.source k := mem_iUnion.mp (T.full_preimage.subset
        ⟨hx,show D.map x ∈ T.tube '' _root_.Dehn.identityTube L d from hxz.symm ▸ hzimage⟩)
  by_cases hj : T.label j = 0
  · simp only [hj,if_true]
    rw [hwhole₀ _ hzimage]
    constructor
    · rintro ⟨x,hx,hxz⟩
      have hxS := D.source_space.symm.subset (Or.inl hx)
      have hv : D.map x = T.tube z := (D.first_value hx).trans hxz
      obtain ⟨k,hk⟩ := hloc x hxS hv
      have hk0 : T.label k = 0 := by
        by_contra hn
        have hkb := hbranch k hk
        simp only [hn,if_false] at hkb
        exact disjoint_left.mp D.disjoint hx hkb
      have hkj : k = j := T.label.injective (hk0.trans hj.symm)
      exact ⟨x,hkj ▸ hk,hv⟩
    · rintro ⟨x,hx,hxz⟩
      have hxf := hbranch j hx
      simp only [hj,if_true] at hxf
      exact ⟨x,hxf,(D.first_value hxf).symm.trans hxz⟩
  · simp only [hj,if_false]
    rw [hwhole₁ _ hzimage]
    constructor
    · rintro ⟨x,hx,hxz⟩
      have hxS := D.source_space.symm.subset (Or.inr ⟨x,hx,rfl⟩)
      have hv : D.map (D.shift x) = T.tube z := (D.second_value x hx).trans hxz
      obtain ⟨k,hk⟩ := hloc (D.shift x) hxS hv
      have hk0 : T.label k ≠ 0 := by
        intro hh
        have hkb := hbranch k hk
        simp only [hh,if_true] at hkb
        exact disjoint_left.mp D.disjoint hkb ⟨x,hx,rfl⟩
      have hkj : k = j := T.label.injective (by
        have hk1 : T.label k = 1 := by omega
        have hj1 : T.label j = 1 := by omega
        exact hk1.trans hj1.symm)
      exact ⟨D.shift x,hkj ▸ hk,hv⟩
    · rintro ⟨x,hx,hxz⟩
      have hxf := hbranch j hx
      simp only [hj,if_false] at hxf
      obtain ⟨y,hy,rfl⟩ := hxf
      exact ⟨y,hy,(D.second_value y hy).symm.trans hxz⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
