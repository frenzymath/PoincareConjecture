import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.OriginalTube



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem proper_strip_returning_rim
    {E : Type*} [TopologicalSpace E] {c : P2 → E} {Q H : Set E}
    (hc : ContinuousOn c source) (hQ : IsClosed Q) (hH : IsClosed H)
    (hdis : Disjoint Q H)
    (hfront : ∀ p ∈ source, c p ∈ Q ∪ H ↔ p.1 = 0 ∨ p.1 = 1)
    (h0 : c (0, 0) ∈ Q) (h1 : c (1, 0) ∈ Q) :
    (∀ p ∈ source, c p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1) ∧
    Disjoint (c '' source) H := by
  have hend (t : ℝ) (ht : t = 0 ∨ t = 1) (hcenter : c (t, 0) ∈ Q) :
      ∀ y ∈ Icc (-1 : ℝ) 1, c (t, y) ∈ Q := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
    let g : Icc (-1 : ℝ) 1 → E := fun y ↦ c (t, y)
    have hg : Continuous g := hc.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun y ↦ ⟨htI, y.property⟩)
    let : PreconnectedSpace (Icc (-1 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hconn : IsPreconnected (g '' univ) := isPreconnected_univ.image g hg.continuousOn
    have hcover : g '' univ ⊆ Q ∪ H := by
      rintro _ ⟨y, _, rfl⟩
      exact (hfront (t, y) ⟨htI, y.property⟩).mpr ht
    intro y hy
    rcases hcover ⟨⟨y, hy⟩, mem_univ _, rfl⟩ with hq | hh
    · exact hq
    · obtain ⟨z, _, hzQ, hzH⟩ := isPreconnected_closed_iff.mp hconn Q H hQ hH hcover
        ⟨c (t, 0), ⟨⟨0, by norm_num⟩, mem_univ _, rfl⟩, hcenter⟩
        ⟨c (t, y), ⟨⟨y, hy⟩, mem_univ _, rfl⟩, hh⟩
      exact (disjoint_left.mp hdis hzQ hzH).elim
  have hends (p : P2) (hp : p ∈ source) (ht : p.1 = 0 ∨ p.1 = 1) : c p ∈ Q := by
    rcases ht with ht | ht
    · simpa only [← ht, Prod.eta] using hend 0 (Or.inl rfl) h0 p.2 hp.2
    · simpa only [← ht, Prod.eta] using hend 1 (Or.inr rfl) h1 p.2 hp.2
  refine ⟨fun p hp ↦ ⟨fun h ↦ (hfront p hp).mp (Or.inl h), hends p hp⟩, ?_⟩
  refine disjoint_left.mpr ?_
  rintro _ ⟨p, hp, rfl⟩ hh
  exact disjoint_left.mp hdis (hends p hp ((hfront p hp).mp (Or.inr hh))) hh

theorem OriginalIntervalTube.returning_source_rims
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D Q₀ H₀ Q₁ H₁ : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hQ₀ : IsClosed Q₀) (hH₀ : IsClosed H₀) (hd₀ : Disjoint Q₀ H₀)
    (hQ₁ : IsClosed Q₁) (hH₁ : IsClosed H₁) (hd₁ : Disjoint Q₁ H₁)
    (hp₀ : ∀ x ∈ S, f₀ x ∈ frontier R ↔ x ∈ Q₀ ∪ H₀)
    (hp₁ : ∀ x ∈ T, f₁ x ∈ frontier R ↔ x ∈ Q₁ ∪ H₁)
    (hC : Disjoint C H₀) (hD : Disjoint D H₁) :
    (∀ p ∈ source, U.first p ∈ Q₀ ↔ p.1 = 0 ∨ p.1 = 1) ∧
    Disjoint (U.first '' source) H₀ ∧
    (∀ p ∈ source, U.second p ∈ Q₁ ↔ p.1 = 0 ∨ p.1 = 1) ∧
    Disjoint (U.second '' source) H₁ := by
  have hfirst (p : P2) (hp : p ∈ source) :
      U.first p ∈ Q₀ ∪ H₀ ↔ p.1 = 0 ∨ p.1 = 1 := by
    rw [← hp₀ _ (U.first_mapsTo hp), U.first_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube false hp)]
    rfl
  have hsecond (p : P2) (hp : p ∈ source) :
      U.second p ∈ Q₁ ∪ H₁ ↔ p.1 = 0 ∨ p.1 = 1 := by
    rw [← hp₁ _ (U.second_mapsTo hp), U.second_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube true hp)]
    rfl
  have hends₀ (t : ℝ) (ht : t = 0 ∨ t = 1) : U.first (t, 0) ∈ Q₀ := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
    have hc : U.first (t, 0) ∈ C := U.first_center.subset ⟨(t, 0), ⟨htI, rfl⟩, rfl⟩
    exact ((hfirst (t, 0) ⟨htI, by norm_num⟩).mpr ht).resolve_right
      (fun hh ↦ disjoint_left.mp hC hc hh)
  have hends₁ (t : ℝ) (ht : t = 0 ∨ t = 1) : U.second (t, 0) ∈ Q₁ := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
    have hc : U.second (t, 0) ∈ D := U.second_center.subset ⟨(t, 0), ⟨htI, rfl⟩, rfl⟩
    exact ((hsecond (t, 0) ⟨htI, by norm_num⟩).mpr ht).resolve_right
      (fun hh ↦ disjoint_left.mp hD hc hh)
  obtain ⟨hf, hfh⟩ := proper_strip_returning_rim U.first_pl.continuousOn hQ₀ hH₀ hd₀
    hfirst (hends₀ 0 (Or.inl rfl)) (hends₀ 1 (Or.inr rfl))
  obtain ⟨hs, hsh⟩ := proper_strip_returning_rim U.second_pl.continuousOn hQ₁ hH₁ hd₁
    hsecond (hends₁ 0 (Or.inl rfl)) (hends₁ 1 (Or.inr rfl))
  exact ⟨hf, hfh, hs, hsh⟩

end PoincareConjecture.M76.Dehn.Annuli
