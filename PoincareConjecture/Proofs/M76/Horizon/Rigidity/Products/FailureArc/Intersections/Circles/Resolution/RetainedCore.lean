import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.ExteriorAnnulus
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

theorem exists_cup_retained_core
    {X : Type*} [TopologicalSpace X] [T2Space X] {A₁ S₁ : Set P2} {L d δ : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) (hδ : 0 < δ) (hδd : δ < d)
    (B₁ : OrientedPolygonCollar L d A₁) (f₁ : P2 → X)
    (hS : IsCompact S₁) (hf : ContinuousOn f₁ S₁) (hfi : InjOn f₁ S₁)
    (houterS : closure B₁.outer.inside ⊆ S₁)
    (τ : C3 → X) {Cup S : Set X}
    (hcap : Cup ∩ (f₁ '' S₁) = f₁ '' closure B₁.inner.inside) (hCS : Cup ⊆ S)
    (hperiod : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
      (v : squareAnnulus L d), (v : P2) = annulusMap L (by linarith) ((s : AddCircle (4 * L)), u) →
        f₁ (B₁.chart v) = τ ((u, u), s))
    (p : AddCircle (4 * L) × I01 → X)
    (hp : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (t : I01),
      p ((s : AddCircle (4 * L)), t) = τ ((d - δ * t, d - δ * t), s)) :
    ∃ Z : Set X, IsClosed Z ∧ Disjoint Cup Z ∧ f₁ '' S₁ ⊆ (S ∪ range p) ∪ Z := by
  classical
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex hd hwidth
  have hAnn : IsCompact (squareAnnulus L d) := hKs ▸ K.isCompact_space_of_finite hK
  let : CompactSpace (squareAnnulus L d) := isCompact_iff_compactSpace.mp hAnn
  let bad : Set P2 := (fun v : squareAnnulus L d ↦ (B₁.chart v : P2)) ''
    {v : squareAnnulus L d | depth L v ≤ d - δ}
  have hbad : IsClosed bad := by
    have hclosed : IsClosed {v : squareAnnulus L d | depth L v ≤ d - δ} :=
      isClosed_le ((continuous_depth L).comp continuous_subtype_val) continuous_const
    exact (hclosed.isCompact.image (continuous_subtype_val.comp B₁.chart.continuous)).isClosed
  let V := B₁.outer.inside \ bad
  have hV : IsOpen V := (B₁.outer.isOpen_inside B₁.outer_simplicial B₁.outer_injective).sdiff hbad
  have hinnerV : closure B₁.inner.inside ⊆ V := by
    intro x hx
    refine ⟨B₁.nested hx, ?_⟩
    rintro ⟨v, hv, hcv⟩
    have hvin : (B₁.chart v : P2) ∈ closure B₁.inner.inside := by
      change (B₁.chart v : P2) = x at hcv
      rwa [hcv]
    have hrim : (B₁.chart v : P2) ∈ B₁.inner.boundary ℝ := by
      rw [← B₁.inner.frontier_inside B₁.inner_simplicial B₁.inner_injective, frontier,
        (B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective).interior_eq]
      exact ⟨hvin, (B₁.carrier.subset (B₁.chart v).property).2⟩
    have hdep := (B₁.inner_depth v).mp hrim
    change depth L (v : P2) ≤ d - δ at hv
    linarith
  have hVcover (x : P2) (hx : x ∈ V) :
      x ∈ closure B₁.inner.inside ∨ f₁ x ∈ range p := by
    by_cases hin : x ∈ closure B₁.inner.inside
    · exact Or.inl hin
    have hxA : x ∈ A₁ := B₁.carrier.symm.subset
      ⟨subset_closure hx.1, fun hh ↦ hin (subset_closure hh)⟩
    let v := B₁.chart.symm ⟨x, hxA⟩
    have hcv : (B₁.chart v : P2) = x := congrArg Subtype.val (B₁.chart.apply_symm_apply _)
    have hlow : d - δ < depth L (v : P2) := by
      by_contra hh
      exact hx.2 ⟨v, le_of_not_gt hh, hcv⟩
    have hupper : depth L (v : P2) ≤ d := (mem_squareAnnulus_iff_depth.mp v.property).2
    let t : I01 := ⟨(d - depth L (v : P2)) / δ,
      div_nonneg (sub_nonneg.mpr hupper) hδ.le,
      (div_le_one hδ).mpr (by linarith)⟩
    have hdt : d - δ * (t : ℝ) = depth L (v : P2) := by
      dsimp [t]
      field_simp
      ring
    obtain ⟨s, hs, hv⟩ := exists_period_parameter_of_depth hd hwidth v
    have hfv := hperiod s hs ⟨depth L v, mem_squareAnnulus_iff_depth.mp v.property⟩ v hv
    have hpv := hp s hs t
    rw [hdt] at hpv
    refine Or.inr ⟨((s : AddCircle (4 * L)), t), ?_⟩
    exact hpv.trans (hfv.symm.trans (congrArg f₁ hcv))
  let Z := f₁ '' (S₁ \ V)
  have hZ : IsClosed Z := ((hS.diff hV).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  refine ⟨Z, hZ, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ hCup ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hcap.subset ⟨hCup, ⟨x, hx.1, rfl⟩⟩
    have hyS := houterS (subset_closure (B₁.nested hy))
    exact hx.2 ((hfi hyS hx.1 hyx) ▸ hinnerV hy)
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxV : x ∈ V
    · rcases hVcover x hxV with hin | hp'
      · exact Or.inl (Or.inl (hCS (hcap.symm.subset ⟨x, hin, rfl⟩).1))
      · exact Or.inl (Or.inr hp')
    · exact Or.inr ⟨x, ⟨hx, hxV⟩, rfl⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
