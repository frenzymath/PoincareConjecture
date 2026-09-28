import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.InteriorEndpointChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.RelativePreimageFrontier
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem plDomain_relative_circle_slab
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (p : ℝ) [Fact (0 < p)] (q : C(R, AddCircle p))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), ∀ x : R, q x = (theta : AddCircle p) →
      ∃ (d : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (T : OpenPartialHomeomorph X V3),
        (d : AddCircle p) = (theta : AddCircle p) ∧ ell.contLinear v = 1 ∧
        (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p))
    (hregB : ∀ theta ∈ ({a, b} : Set ℝ), ∀ x : R,
      (x : X) ∈ frontier R → q x = (theta : AddCircle p) →
      ∃ (d : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3) (T : OpenPartialHomeomorph X V3),
        (d : AddCircle p) = (theta : AddCircle p) ∧ psi.contLinear u = 1 ∧
        ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
        (x : X) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
        (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
        (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
        ∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + d : ℝ) : AddCircle p)) :
    let N : Set X := Subtype.val '' (q ⁻¹' AddCircle.closedIntervalArc p a b)
    PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
      Subtype.val '' (q ⁻¹' {(a : AddCircle p), (b : AddCircle p)}) := by
  classical
  intro N
  let arc := AddCircle.closedIntervalArc p a b
  have harc : IsClosed arc := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  have hN : IsCompact N := (harc.preimage q.continuous).isCompact.image continuous_subtype_val
  have hNR : N ⊆ R := by rintro _ ⟨y, _, rfl⟩; exact y.property
  let M := (N ∩ frontier R) ∪ Subtype.val '' (q ⁻¹' {(a : AddCircle p), (b : AddCircle p)})
  have hfront : frontier N ⊆ M := by
    have h := relative_preimage_frontier_subset hR q harc
    rw [AddCircle.frontier_closedIntervalArc p ha hab.le hb] at h
    exact h
  have hmem (y : X) : y ∈ N ↔ ∃ hy : y ∈ R, q ⟨y, hy⟩ ∈ arc := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hy, hq⟩
      exact ⟨⟨y, hy⟩, hq, rfl⟩
  have hMR : M ⊆ R := by
    rintro x (hx | ⟨y, _, rfl⟩)
    · exact hNR hx.1
    · exact y.property
  have hcharts (x : X) (hx : x ∈ M) :
      ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (G : OpenPartialHomeomorph X V3),
        ell.contLinear v = 1 ∧ x ∈ G.source ∧ ell (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ G.source, y ∈ N ↔ 0 ≤ ell (G y) := by
    let x' : R := ⟨x, hMR hx⟩
    by_cases hendpoint : q x' ∈ ({(a : AddCircle p), (b : AddCircle p)} : Set _)
    · obtain ⟨theta, htheta, hxt⟩ : ∃ theta ∈ ({a, b} : Set ℝ), q x' = (theta : AddCircle p) := by
        rcases hendpoint with h | h
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨b, Or.inr rfl, h⟩
      by_cases hxB : x ∈ frontier R
      · obtain ⟨d, psi, ell, u, v, T, hd, hpu, hlv, hpv, hxT, hlx, hpx,
          hT, hTR, hTB, hq⟩ := hregB theta htheta x' hxB hxt
        obtain ⟨lambda, G, hxG, _, hpxG, hG, _, hGN, _, _⟩ :=
          exists_relative_circle_endpoint_chart e p q ha hab hb htheta hd
            psi ell u v T hpu hlv hpv hxT hpx hlx hT hTR hTB hq
        exact ⟨psi, u, G, hpu, hxG, hpxG, hG,
          fun y hy => (hmem y).trans (hGN y hy)⟩
      · obtain ⟨d, ell, v, T, hd, hlv, hxT, hlx, hT, hq⟩ := hreg theta htheta x' hxt
        obtain ⟨T', hTs, hTT, hT'⟩ :=
          exists_compatible_chart_restriction e T hT (isOpen_interior (s := R))
        have hxT' : x ∈ T'.source := hTs.symm.subset
          ⟨hxT, (mem_interior_iff_notMem_frontier x'.property).mpr hxB⟩
        have hlx' : ell (T' x) = 0 := by rw [hTT]; exact hlx
        have hTR : T'.source ⊆ R := fun y hy => interior_subset (hTs.subset hy).2
        have hq' (y : R) (hy : (y : X) ∈ T'.source) :
            q y = ((ell (T' y) + d : ℝ) : AddCircle p) := by
          rw [hTT]
          exact hq y (hTs.subset hy).1
        obtain ⟨lambda, w, G, hlw, hxG, _, hlxG, hG, hGN⟩ :=
          exists_interior_circle_endpoint_chart e p q ha hab hb htheta hd
            ell v T' hlv hxT' hlx' hTR hT' hq'
        exact ⟨lambda, w, G, hlw, hxG, hlxG, hG,
          fun y hy => (hmem y).trans (hGN y hy)⟩
    · have hxold : x ∈ N ∩ frontier R := by
        rcases hx with hx | ⟨y, hy, hyx⟩
        · exact hx
        · have hyx' : y = x' := Subtype.ext hyx
          exact False.elim (hendpoint (hyx' ▸ hy))
      have hqx : q x' ∈ arc := by
        obtain ⟨hxR, hqx⟩ := (hmem x).mp hxold.1
        exact hqx
      have hqxI : q x' ∈ interior arc := by
        apply (mem_interior_iff_notMem_frontier hqx).mpr
        simpa only [arc, AddCircle.frontier_closedIntervalArc p ha hab.le hb] using hendpoint
      obtain ⟨U, hU, hUq⟩ := isOpen_induced_iff.mp (isOpen_interior.preimage q.continuous)
      have hxU : x ∈ U := hUq.symm.subset hqxI
      obtain ⟨ell, v, T, hlv, hxT, hlx, hT, hTR⟩ := he.halfspace x hxold.2
      obtain ⟨G, hGs, hGT, hG⟩ := exists_compatible_chart_restriction e T hT hU
      refine ⟨ell, v, G, hlv, hGs.symm.subset ⟨hxT, hxU⟩, ?_, hG, ?_⟩
      · rw [hGT]; exact hlx
      · intro y hy
        rw [hGT, ← hTR y (hGs.subset hy).1]
        constructor
        · exact fun hyN => hNR hyN
        · intro hyR
          have hyq : q ⟨y, hyR⟩ ∈ interior arc := hUq.subset (hGs.subset hy).2
          exact (hmem y).mpr ⟨hyR, interior_subset hyq⟩
  have hPL : PLDomain e N :=
    ⟨he.cover, he.compatible, hN.isClosed, fun x hx => hcharts x (hfront hx)⟩
  refine ⟨hPL, Subset.antisymm hfront ?_⟩
  intro x hx
  obtain ⟨ell, v, G, hv, hxG, hxzero, _, hGN⟩ := hcharts x hx
  have hn : ell.toAffineMap.linear ≠ 0 := by
    intro hn
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [hn, LinearMap.zero_apply] at hv'
    exact zero_ne_one hv'
  exact ((G.isImage_frontier_of_affine_nonneg ell hn hGN).apply_mem_iff hxG).mp hxzero

end PoincareConjecture.M76.HamiltonIntervalTorus
