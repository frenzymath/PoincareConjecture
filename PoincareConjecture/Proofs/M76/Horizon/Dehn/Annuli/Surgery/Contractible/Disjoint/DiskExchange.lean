import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedSource









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_synchronized_inner_disk_exchange
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁) :
    ∃ H : closure B₀.inner.inside ≃ₜ closure B₁.inner.inside,
      H.IsFinitePL ∧
      (∀ x : closure B₀.inner.inside,
        (H x : P2) ∈ B₁.inner.boundary ℝ ↔ (x : P2) ∈ B₀.inner.boundary ℝ) ∧
      (∀ (p : squareAnnulus L d) (hp : depth L p = d),
        (H ⟨B₀.chart p, (B₀.inner.isFinitePLBallPair_closed_inside
          B₀.inner_simplicial B₀.inner_injective).1 ((B₀.inner_depth p).mpr hp)⟩ : P2) =
          B₁.chart p) ∧
      (∀ (p : squareAnnulus L d) (hp : depth L p = d),
        (H.symm ⟨B₁.chart p, (B₁.inner.isFinitePLBallPair_closed_inside
          B₁.inner_simplicial B₁.inner_injective).1 ((B₁.inner_depth p).mpr hp)⟩ : P2) =
          B₀.chart p) := by
  obtain ⟨eb, heb, _, _, hperiod⟩ := exists_synchronized_collar_boundary_homeomorph
    B₀.inner B₁.inner B₀.inner_simplicial B₀.inner_injective
    (oriented_collar_boundary_subsets B₀).2 (oriented_collar_boundary_subsets B₁).2
    B₀.chart B₁.chart B₀.chart_PL B₁.chart_PL B₀.inner_depth B₁.inner_depth
  have hI₀ := B₀.inner.isFinitePLBallPair_closed_inside B₀.inner_simplicial B₀.inner_injective
  have hI₁ := B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective
  obtain ⟨H, hH, hHb, hHmem⟩ := hI₀.exists_extension hI₁ eb heb
  have hp (p : squareAnnulus L d) (hd : depth L p = d) :
      (H ⟨B₀.chart p, hI₀.1 ((B₀.inner_depth p).mpr hd)⟩ : P2) = B₁.chart p :=
    (congrArg Subtype.val (hHb ⟨B₀.chart p, (B₀.inner_depth p).mpr hd⟩)).trans
      (hperiod p hd)
  refine ⟨H, hH, fun x ↦ (hHmem x).symm, hp, ?_⟩
  intro p hd
  have he : H ⟨B₀.chart p, hI₀.1 ((B₀.inner_depth p).mpr hd)⟩ =
      ⟨B₁.chart p, hI₁.1 ((B₁.inner_depth p).mpr hd)⟩ := Subtype.ext (hp p hd)
  have he' := congrArg H.symm he
  simpa only [Homeomorph.symm_apply_apply] using (congrArg Subtype.val he').symm

end PoincareConjecture.M76.Dehn.Annuli
