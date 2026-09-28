import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Tubes.SelectedTube



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem interval_tube_source_preimages
    {E X : Type*} {S : Bool → Set E} {f : E → X}
    (c : Bool → P2 → E) (τ : C3 → X)
    (hdis : Disjoint (S false) (S true))
    (hsub : ∀ j, MapsTo (c j) source (S j))
    (hsheet : ∀ j p, p ∈ source → f (c j p) = τ (originalStripSheet j p))
    (hfull : (S false ∪ S true) ∩ f ⁻¹' (τ '' tube) =
      c false '' source ∪ c true '' source) :
    ∀ j, S j ∩ f ⁻¹' (τ '' tube) = c j '' source := by
  intro j
  apply Subset.antisymm
  · rintro x ⟨hx,hxT⟩
    have hxS : x ∈ S false ∪ S true := by cases j; exact Or.inl hx; exact Or.inr hx
    have hxpre := hfull.subset ⟨hxS,hxT⟩
    cases j
    · exact hxpre.resolve_right (by
        rintro ⟨p,hp,hpx⟩
        exact disjoint_left.mp hdis hx (hpx ▸ hsub true hp))
    · exact hxpre.resolve_left (by
        rintro ⟨p,hp,hpx⟩
        exact disjoint_left.mp hdis (hpx ▸ hsub false hp) hx)
  · rintro x ⟨p,hp,rfl⟩
    exact ⟨hsub j hp,⟨originalStripSheet j p,originalStripSheet_mem_tube j hp,
      (hsheet j p hp).symm⟩⟩

theorem interval_tube_whole_surface_traces
    {E X : Type*} {S : Bool → Set E} {f : E → X}
    (c : Bool → P2 → E) (τ : C3 → X)
    (hdis : Disjoint (S false) (S true))
    (hsub : ∀ j, MapsTo (c j) source (S j)) (hτ : InjOn τ tube)
    (hsheet : ∀ j p, p ∈ source → f (c j p) = τ (originalStripSheet j p))
    (hfull : (S false ∪ S true) ∩ f ⁻¹' (τ '' tube) =
      c false '' source ∪ c true '' source) :
    ∀ (j : Bool) z, z ∈ tube →
      (τ z ∈ f '' S j ↔ z.1.2 = if j then -z.1.1 else z.1.1) := by
  intro j z hz
  constructor
  · rintro ⟨x,hx,hxz⟩
    have hxS : x ∈ S false ∪ S true := by cases j; exact Or.inl hx; exact Or.inr hx
    have hxpre := hfull.subset ⟨hxS,⟨z,hz,hxz.symm⟩⟩
    have hxp : ∃ p ∈ source, c j p = x := by
      cases j
      · rcases hxpre with h | ⟨p,hp,hpx⟩
        · exact h
        · exact (disjoint_left.mp hdis hx (hpx ▸ hsub true hp)).elim
      · rcases hxpre with ⟨p,hp,hpx⟩ | h
        · exact (disjoint_left.mp hdis (hpx ▸ hsub false hp) hx).elim
        · exact h
    obtain ⟨p,hp,rfl⟩ := hxp
    have heq := hτ (originalStripSheet_mem_tube j hp) hz ((hsheet j p hp).symm.trans hxz)
    rw [←heq]
    rfl
  · intro hdiag
    let p : P2 := (z.2,z.1.1)
    have hp : p ∈ source := ⟨hz.2,hz.1.1⟩
    have heq : originalStripSheet j p = z := by
      exact Prod.ext (Prod.ext rfl hdiag.symm) rfl
    refine ⟨c j p,hsub j hp,?_⟩
    rw [hsheet j p hp,heq]

end PoincareConjecture.M76.Dehn.Annuli
