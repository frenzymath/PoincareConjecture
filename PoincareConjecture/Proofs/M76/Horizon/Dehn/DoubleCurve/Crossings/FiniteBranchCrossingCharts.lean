import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.OrderedCrossingChart









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1


theorem isCompact_sdiff_of_open_in_disk {P L : Set V2}
    (hP : IsCompact P) (hPD : P ⊆ D2)
    (hL : IsOpen ((Subtype.val : D2 → V2) ⁻¹' L)) : IsCompact (P \ L) := by
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP
  have ho : IsOpen ((Subtype.val : P → V2) ⁻¹' L) :=
    hL.preimage (continuous_subtype_val.subtype_mk (fun x ↦ hPD x.property))
  have heq : (Subtype.val : P → V2) '' ((Subtype.val : P → V2) ⁻¹' L)ᶜ = P \ L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hn⟩
      exact ⟨⟨x, hx⟩, hn, rfl⟩
  rw [← heq]
  exact ho.isClosed_compl.isCompact.image continuous_subtype_val



theorem RawCrossingChart.exists_finite_branch_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X} {x y : V2}
    (C : RawCrossingChart e f R x y) (hf : PolyhedralPLInCharts e f D2)
    {P Q : Set V2} (hP : IsCompact P) (hQ : IsCompact Q)
    (hPD : P ⊆ D2) (hQD : Q ⊆ D2)
    (hiP : InjOn f P) (hiQ : InjOn f Q) (hx : x ∈ P) (hy : y ∈ Q)
    (hxy : f x = f y) {O A : Set X} (hO : IsOpen O) (hxO : f x ∈ O)
    (hfull : ∀ z ∈ D2, f z ∈ O → z ∈ P ∪ Q)
    (hinter : O ∩ (f '' P ∩ f '' Q) = A) :
    ∃ T : OpenPartialHomeomorph X V3,
      f x ∈ T.source ∧ T.source ⊆ O ∧
      (∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ z ∈ T.source, z ∈ f '' P ↔ T z 0 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ T.source, z ∈ f '' Q ↔ T z 1 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ T.source, z ∈ A ↔ z ∈ R ∧ T z 0 = 0 ∧ T z 1 = 0) ∧
      (T.source ⊆ interior R ∨
        ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ T z 2) ∧
          ∀ z ∈ T.source, z ∈ frontier R ↔ T z 2 = 0)) ∧
      ∃ D : RawCrossingChart e f R x y, x ∈ D.left ∧ y ∈ D.right ∧
        (T : X → V3) = D.chart ∧ T.source ⊆ D.chart.source := by
  obtain ⟨D, hxL, hyR⟩ := C.exists_ordered
  have hPc : IsClosed (f '' (P \ D.left)) :=
    ((isCompact_sdiff_of_open_in_disk hP hPD D.left_open).image_of_continuousOn
      (hf.continuousOn.mono (sdiff_subset.trans hPD))).isClosed
  have hQc : IsClosed (f '' (Q \ D.right)) :=
    ((isCompact_sdiff_of_open_in_disk hQ hQD D.right_open).image_of_continuousOn
      (hf.continuousOn.mono (sdiff_subset.trans hQD))).isClosed
  let W := O \ (f '' (P \ D.left) ∪ f '' (Q \ D.right))
  have hW : IsOpen W := hO.sdiff (hPc.union hQc)
  have hxW : f x ∈ W := by
    refine ⟨hxO, ?_⟩
    rintro (⟨a, ha, hfa⟩ | ⟨a, ha, hfa⟩)
    · exact ha.2 ((hiP ha.1 hx hfa).symm ▸ hxL)
    · exact ha.2 ((hiQ ha.1 hy (hfa.trans hxy)).symm ▸ hyR)
  have hPcut (z : V2) (hz : z ∈ P) (hzW : f z ∈ W) : z ∈ D.left := by
    by_contra hn
    exact hzW.2 (Or.inl ⟨z, ⟨hz, hn⟩, rfl⟩)
  have hQcut (z : V2) (hz : z ∈ Q) (hzW : f z ∈ W) : z ∈ D.right := by
    by_contra hn
    exact hzW.2 (Or.inr ⟨z, ⟨hz, hn⟩, rfl⟩)
  have hLim (z : X) (hz : z ∈ W) : z ∈ f '' P ↔ z ∈ f '' D.left := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, hPcut a ha hz, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases hfull a (D.left_subset ha) hz.1 with hp | hq
      · exact ⟨a, hp, rfl⟩
      · exact (disjoint_left.mp D.disjoint ha (hQcut a hq hz)).elim
  have hRim (z : X) (hz : z ∈ W) : z ∈ f '' Q ↔ z ∈ f '' D.right := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, hQcut a ha hz, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rcases hfull a (D.right_subset ha) hz.1 with hp | hq
      · exact (disjoint_left.mp D.disjoint (hPcut a hp hz) ha).elim
      · exact ⟨a, hq, rfl⟩
  let T := D.chart.restrOpen W hW
  have hleft (z : X) (hz : z ∈ T.source) :
      z ∈ f '' P ↔ T z 0 = 0 ∧ z ∈ R :=
    (hLim z hz.2).trans (D.left_image z hz.1)
  have hright (z : X) (hz : z ∈ T.source) :
      z ∈ f '' Q ↔ T z 1 = 0 ∧ z ∈ R :=
    (hRim z hz.2).trans (D.right_image z hz.1)
  refine ⟨T, ⟨D.point, hxW⟩, fun _ hz ↦ hz.2.1, ?_, hleft, hright, ?_, ?_,
    D, hxL, hyR, rfl, fun _ hz ↦ hz.1⟩
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (D.compatible k)).mono
      ((e k).symm.trans T).open_source (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  · intro z hz
    rw [← hinter, mem_inter_iff, mem_inter_iff, hleft z hz, hright z hz]
    exact ⟨fun h ↦ ⟨h.2.1.2, h.2.1.1, h.2.2.1⟩,
      fun h ↦ ⟨hz.2.1, ⟨h.2.1, h.1⟩, h.2.2, h.1⟩⟩
  · rcases D.region with hin | ⟨hr, hfr⟩
    · exact Or.inl (fun _ hz ↦ hin hz.1)
    · exact Or.inr ⟨fun z hz ↦ hr z hz.1, fun z hz ↦ hfr z hz.1⟩

end PoincareConjecture.M76.Dehn
