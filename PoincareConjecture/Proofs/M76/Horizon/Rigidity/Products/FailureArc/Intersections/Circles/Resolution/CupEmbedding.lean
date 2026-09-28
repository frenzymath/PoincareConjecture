import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.CupMap

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)

theorem cup_map_injective
    {X : Type*} {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside)
    {f a v : P2 → X}
    (hfi : InjOn f (closure B₁.inner.inside))
    (hai : Function.Injective (fun x : squareAnnulus L d ↦ a x))
    (hvi : ∀ x : closure B₁.inner.inside, v (H x) = f x)
    (hva : ∀ p : squareAnnulus L d, v (B₀.chart p) = a p)
    (hperiod : ∀ (p : squareAnnulus L d) (hp : depth L p = d),
      (H ⟨B₁.chart p, (B₁.inner.isFinitePLBallPair_closed_inside
        B₁.inner_simplicial B₁.inner_injective).1 ((B₁.inner_depth p).mpr hp)⟩ : P2) =
          B₀.chart p)
    (hainner : ∀ p : squareAnnulus L d, depth L p = d → a p = f (B₁.chart p))
    (hcontact : ∀ p : squareAnnulus L d, a p ∈ f '' closure B₁.inner.inside → depth L p = d) :
    InjOn v (closure B₀.outer.inside) := by
  have hrep (x : P2) (hx : x ∈ closure B₀.outer.inside) :
      (∃ y : closure B₁.inner.inside, (H y : P2) = x) ∨
      (∃ p : squareAnnulus L d, (B₀.chart p : P2) = x) := by
    by_cases hin : x ∈ closure B₀.inner.inside
    · exact Or.inl ⟨H.symm ⟨x, hin⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩
    · have hxA : x ∈ A₀ := B₀.carrier.symm.subset ⟨hx, fun hh ↦ hin (subset_closure hh)⟩
      exact Or.inr ⟨B₀.chart.symm ⟨x, hxA⟩, congrArg Subtype.val (B₀.chart.apply_symm_apply _)⟩
  have hcross (y : closure B₁.inner.inside) (p : squareAnnulus L d)
      (h : f y = a p) : (H y : P2) = B₀.chart p := by
    have hd := hcontact p ⟨y, y.property, h⟩
    let z : closure B₁.inner.inside := ⟨B₁.chart p,
      (B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective).1
        ((B₁.inner_depth p).mpr hd)⟩
    have hyz : y = z := Subtype.ext (hfi y.property z.property (h.trans (hainner p hd)))
    rw [hyz]
    exact hperiod p hd
  intro x hx y hy hxy
  rcases hrep x hx with ⟨u, rfl⟩ | ⟨p, rfl⟩ <;>
    rcases hrep y hy with ⟨w, rfl⟩ | ⟨q, rfl⟩
  · rw [hvi, hvi] at hxy
    exact congrArg (fun z : closure B₁.inner.inside ↦ (H z : P2))
      (Subtype.ext (hfi u.property w.property hxy))
  · rw [hvi, hva] at hxy
    exact hcross u q hxy
  · rw [hva, hvi] at hxy
    exact (hcross w p hxy.symm).symm
  · rw [hva, hva] at hxy
    exact congrArg (fun z : squareAnnulus L d ↦ (B₀.chart z : P2)) (hai hxy)

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
