import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport
import PoincareConjecture.Proofs.Horizon.Topology.Maps.ProperRestriction











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem exists_contMDiff_proper_band_localization
    (d : M → ℝ) (hd : Continuous d) {u : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    {r0 r1 R0 R1 a b ε : ℝ}
    (hr : r0 < r1) (hcore : r1 < R0) (hR : R0 < R1)
    (ha : 0 < a) (_hab : a < b) (hinner : r1 + ε < a) (houter : b < R0 - ε)
    (hcompact0 : IsCompact {x | d x ≤ r0}) (hcompactR0 : IsCompact {x | d x ≤ R0})
    (herr : ∀ x, r0 ≤ d x → d x ≤ R1 → |u x - d x| ≤ ε) :
    ∃ f : M → ℝ, ∃ K : Set M,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ IsCompact K ∧ f ⁻¹' Ioo a b ⊆ K ∧
      (∀ x, r1 < d x → d x < R0 → f =ᶠ[𝓝 x] u) ∧
      (∀ x, f x ∈ Ioo a b → r1 < d x ∧ d x < R0 ∧ f =ᶠ[𝓝 x] u) ∧
      IsProperMap ((Ioo a b).restrictPreimage f) := by
  obtain ⟨ψ, hψ, hψcompact, hψsupport, hψbounds, hψone⟩ :=
    exists_contMDiff_cutoff_of_isCompact (n := n) hcompact0
      (isOpen_lt hd continuous_const) (fun x hx => hx.trans_lt hr)
  obtain ⟨θ, hθ, hθcompact, hθsupport, hθbounds, hθone⟩ :=
    exists_contMDiff_cutoff_of_isCompact (n := n) hcompactR0
      (isOpen_lt hd continuous_const) (fun x hx => hx.trans_lt hR)
  let Q := b + 1
  let f : M → ℝ := fun x => θ x * (1 - ψ x) * u x + (1 - θ x) * Q
  have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
    ((hθ.mul (contMDiff_const.sub hψ)).mul hu).add
      ((contMDiff_const.sub hθ).mul contMDiff_const)
  have hQ : b < Q := by dsimp only [Q]; linarith
  have hψzero (x : M) (hx : r1 ≤ d x) : ψ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    exact (hψsupport hxs).not_ge hx
  have hlow (x : M) (hx : d x ≤ r1) : f x < a := by
    have hθx : θ x = 1 := (hθone x (hx.trans hcore.le)).self_of_nhds
    have heq : f x = (1 - ψ x) * u x := by simp only [f, hθx]; ring
    rw [heq]
    by_cases hx0 : d x ≤ r0
    · have hψx : ψ x = 1 := (hψone x hx0).self_of_nhds
      simpa only [hψx, sub_self, zero_mul] using ha
    · have hx0' : r0 ≤ d x := (lt_of_not_ge hx0).le
      have he := (abs_le.mp (herr x hx0' (hx.trans (hcore.le.trans hR.le)))).2
      have hub : u x < a := by linarith
      have hp := hψbounds x
      by_cases hu0 : u x ≤ 0
      · have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp.2) hu0
        linarith
      · have hu0' : 0 ≤ u x := (lt_of_not_ge hu0).le
        have hprod := mul_nonneg hp.1 hu0'
        nlinarith
  have hhigh (x : M) (hx : R0 ≤ d x) : b < f x := by
    have hψx : ψ x = 0 := hψzero x (hcore.le.trans hx)
    have heq : f x = θ x * u x + (1 - θ x) * Q := by simp only [f, hψx]; ring
    rw [heq]
    by_cases hxR : d x < R1
    · have he := (abs_le.mp (herr x (hr.le.trans (hcore.le.trans hx)) hxR.le)).1
      have hbu : b < u x := by linarith
      have hmin : b < min (u x) Q := lt_min hbu hQ
      have hleft := mul_le_mul_of_nonneg_left (min_le_left (u x) Q) (hθbounds x).1
      have hright := mul_le_mul_of_nonneg_left (min_le_right (u x) Q)
        (sub_nonneg.mpr (hθbounds x).2)
      nlinarith
    · have hθx : θ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hxs => hxR (hθsupport hxs))
      simpa only [hθx, zero_mul, sub_zero, one_mul, zero_add] using hQ
  have hagree (x : M) (hx1 : r1 < d x) (hx0 : d x < R0) : f =ᶠ[𝓝 x] u := by
    have hxs : x ∉ tsupport ψ := fun hx => (hψsupport hx).not_ge hx1.le
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs, hθone x hx0.le] with y hyψ hyθ
    simp only [Pi.zero_apply] at hyψ
    simp only [Pi.one_apply] at hyθ
    simp only [f, hyψ, hyθ, sub_zero, one_mul, sub_self, zero_mul, add_zero]
  have hband (x : M) (hx : f x ∈ Ioo a b) :
      r1 < d x ∧ d x < R0 ∧ f =ᶠ[𝓝 x] u := by
    have hx1 : r1 < d x := by
      by_contra h
      have hl := hlow x (le_of_not_gt h)
      linarith [hx.1]
    have hx0 : d x < R0 := by
      by_contra h
      have hh := hhigh x (le_of_not_gt h)
      linarith [hx.2]
    exact ⟨hx1, hx0, hagree x hx1 hx0⟩
  have hcontained : f ⁻¹' Ioo a b ⊆ tsupport θ := by
    intro x hx
    by_contra hxs
    have hθx : θ x = 0 := image_eq_zero_of_notMem_tsupport hxs
    have hfx : f x = Q := by simp only [f, hθx, zero_mul, sub_zero, one_mul, zero_add]
    have hxb : f x < b := hx.2
    rw [hfx] at hxb
    linarith
  exact ⟨f, tsupport θ, hf, hθcompact, hcontained, hagree, hband,
    Poincare.isProperMap_real_restrictPreimage_of_isCompact hf.continuous (Ioo a b)
      hθcompact hcontained⟩

end PoincareConjecture
