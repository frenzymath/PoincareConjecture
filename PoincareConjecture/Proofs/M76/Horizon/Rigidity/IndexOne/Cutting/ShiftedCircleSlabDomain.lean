import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.CircleSlabDomain



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem plDomain_relative_shifted_circle_slab
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (p : ℝ) [Fact (0 < p)] (q : C(R, AddCircle p))
    {c a b : ℝ} (ha : c < a) (hab : a < b) (hb : b < c + p)
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
  let q' : C(R, AddCircle p) := ⟨fun x => q x - (c : AddCircle p),
    q.continuous.sub continuous_const⟩
  have hphase (x : R) (t : ℝ) : q' x = ((t - c : ℝ) : AddCircle p) ↔
      q x = (t : AddCircle p) := by
    change q x - (c : AddCircle p) = ((t - c : ℝ) : AddCircle p) ↔ _
    rw [AddCircle.coe_sub, sub_left_inj]
  have hphase' (x : R) (t : ℝ) : q' x = (t : AddCircle p) ↔
      q x = ((t + c : ℝ) : AddCircle p) := by
    simpa only [add_sub_cancel_right] using hphase x (t + c)
  have htheta (t : ℝ) (ht : t ∈ ({a - c, b - c} : Set ℝ)) :
      t + c ∈ ({a, b} : Set ℝ) := by
    rcases ht with rfl | rfl <;> simp
  have harc : q' ⁻¹' AddCircle.closedIntervalArc p (a - c) (b - c) =
      q ⁻¹' AddCircle.closedIntervalArc p a b := by
    ext x
    constructor
    · rintro ⟨t, ht, htx⟩
      exact ⟨t + c, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ((hphase' x t).mp htx.symm).symm⟩
    · rintro ⟨t, ht, htx⟩
      exact ⟨t - c, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        ((hphase x t).mpr htx.symm).symm⟩
  have hend : q' ⁻¹' {((a - c : ℝ) : AddCircle p), ((b - c : ℝ) : AddCircle p)} =
      q ⁻¹' {(a : AddCircle p), (b : AddCircle p)} := by
    ext x
    simp only [mem_preimage, mem_insert_iff, mem_singleton_iff, hphase]
  have h := plDomain_relative_circle_slab e he hR p q'
    (by linarith : 0 < a - c) (by linarith : a - c < b - c)
    (by linarith : b - c < p) ?_ ?_
  · simpa only [harc, hend] using h
  · intro theta ht x hx
    obtain ⟨d, ell, v, T, hd, hv, hxT, hz, hT, hq⟩ :=
      hreg (theta + c) (htheta theta ht) x ((hphase' x theta).mp hx)
    refine ⟨d - c, ell, v, T, ?_, hv, hxT, hz, hT, ?_⟩
    · rw [AddCircle.coe_sub, hd, AddCircle.coe_add, add_sub_cancel_right]
    · intro y hy
      change q y - (c : AddCircle p) = _
      rw [hq y hy, ← AddCircle.coe_sub]
      congr 1
      ring
  · intro theta ht x hxB hx
    obtain ⟨d, psi, ell, u, v, T, hd, hpu, hlv, hpv, hxT, hlx, hpx,
        hT, hTR, hTB, hq⟩ :=
      hregB (theta + c) (htheta theta ht) x hxB ((hphase' x theta).mp hx)
    refine ⟨d - c, psi, ell, u, v, T, ?_, hpu, hlv, hpv, hxT, hlx, hpx,
      hT, hTR, hTB, ?_⟩
    · rw [AddCircle.coe_sub, hd, AddCircle.coe_add, add_sub_cancel_right]
    · intro y hy
      change q y - (c : AddCircle p) = _
      rw [hq y hy, ← AddCircle.coe_sub]
      congr 1
      ring

end PoincareConjecture.M76.HamiltonIntervalTorus

