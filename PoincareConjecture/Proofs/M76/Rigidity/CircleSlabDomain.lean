import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleEndpointHalfspace
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem circle_slab_PLDomain
    {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (p : ℝ) [Fact (0 < p)] (q : C(X, AddCircle p))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hregular : ∀ c ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)),
      ∀ x : X, q x = c →
        ∃ (d : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
          (G : OpenPartialHomeomorph X V3),
          (d : AddCircle p) = c ∧ ell.contLinear v = 1 ∧
          x ∈ G.source ∧ ell (G x) = 0 ∧
          (∀ j, (e j).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ G.source, q y = ((ell (G y) + d : ℝ) : AddCircle p)) ∧
          ∀ y ∈ G.source, q y = c ↔ ell (G y) = 0) :
    let R := q ⁻¹' AddCircle.closedIntervalArc p a b
    IsCompact R ∧ PLDomain e R ∧
      frontier R = q ⁻¹' {(a : AddCircle p), (b : AddCircle p)} := by
  let R := q ⁻¹' AddCircle.closedIntervalArc p a b
  let S := q ⁻¹' {(a : AddCircle p), (b : AddCircle p)}
  have hR : IsClosed R :=
    (AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage q.continuous
  have hfront : frontier R ⊆ S := by
    have h := q.continuous.frontier_preimage_subset (AddCircle.closedIntervalArc p a b)
    simpa only [AddCircle.frontier_closedIntervalArc p ha hab.le hb] using h
  have hhalf (x : X) (hx : x ∈ S) :
      ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (G : OpenPartialHomeomorph X V3),
        ell.contLinear v = 1 ∧ x ∈ G.source ∧ ell (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ G.source, y ∈ R ↔ 0 ≤ ell (G y) := by
    have htheta : ∃ theta : ℝ, (theta = a ∨ theta = b) ∧ q x = (theta : AddCircle p) := by
      rcases hx with hx | hx
      · exact ⟨a, Or.inl rfl, hx⟩
      · exact ⟨b, Or.inr rfl, hx⟩
    obtain ⟨theta, ht, hqx⟩ := htheta
    have htS : (theta : AddCircle p) ∈
        ({(a : AddCircle p), (b : AddCircle p)} : Set (AddCircle p)) := by
      rcases ht with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    obtain ⟨d, ell, v, G, hd, hv, hxG, hzero, hG, hqG, _⟩ :=
      hregular (theta : AddCircle p) htS x hqx
    exact OpenPartialHomeomorph.exists_circle_endpoint_halfspace e p q
      ha hab hb ht hd ell v G hv hxG hzero hG hqG
  have he : PLDomain e R :=
    ⟨hcover, hcompat, hR, fun x hx => hhalf x (hfront hx)⟩
  refine ⟨hR.isCompact, he, subset_antisymm hfront ?_⟩
  intro x hx
  obtain ⟨ell, v, G, hv, hxG, hzero, _, hset⟩ := hhalf x hx
  have hxR : x ∈ R := (hset x hxG).mpr (by rw [hzero])
  refine ⟨subset_closure hxR, ?_⟩
  intro hxi
  have hpos := (G.isImage_interior_of_affine_nonneg ell v hv hset).apply_mem_iff hxG
  have h : 0 < ell (G x) := hpos.mpr hxi
  rw [hzero] at h
  exact lt_irrefl 0 h

end PoincareConjecture.M76
