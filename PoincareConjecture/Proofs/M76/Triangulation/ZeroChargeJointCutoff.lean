import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLipschitz
import Mathlib.Algebra.Order.Group.MinMax

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_transverse_lipschitz [FiniteDimensional ℝ E]
    {Z : E → ℝ} {T : Set E} (hZ : FinitePiecewiseAffineOn Z T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ T, ∀ y ∈ T,
      |Z x - Z y| ≤ L * ‖x - y‖ := by
  obtain ⟨K, hK, hconv, hTK⟩ := hZ.isCompact.exists_finite_convex_neighborhood
  obtain ⟨f, hf, heq, _, _⟩ := hZ.exists_supported_extension K hK
    (hTK.trans interior_subset) isOpen_univ (subset_univ T)
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith hconv
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro x hx y hy
  have h := hL.dist_le_mul x (interior_subset (hTK hx)) y (interior_subset (hTK hy))
  simpa only [heq hx, heq hy, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using h

noncomputable def slowTimeCutoff (R epsilon t z : ℝ) : ℝ :=
  min t ((epsilon / R) * (R - |z|))

theorem slowTimeCutoff_mem {R epsilon t z : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (ht : t ∈ Icc 0 epsilon) (hz : z ∈ Icc (-R) R) :
    slowTimeCutoff R epsilon t z ∈ Icc 0 epsilon := by
  refine ⟨le_min ht.1 (mul_nonneg (div_nonneg hepsilon hR.le)
    (sub_nonneg.mpr (abs_le.mpr hz))), ?_⟩
  exact (min_le_left _ _).trans ht.2

theorem slowTimeCutoff_zero {R epsilon t : ℝ} (hR : 0 < R) (ht : t ≤ epsilon) :
    slowTimeCutoff R epsilon t 0 = t := by
  simp only [slowTimeCutoff, abs_zero, sub_zero, div_mul_cancel₀ _ hR.ne']
  exact min_eq_left ht

theorem slowTimeCutoff_rim {R epsilon t z : ℝ} (ht : 0 ≤ t) (hz : |z| = R) :
    slowTimeCutoff R epsilon t z = 0 := by
  simp only [slowTimeCutoff, hz, sub_self, mul_zero, min_eq_right ht]

theorem slowTimeCutoff_abs_sub_le {R epsilon : ℝ} (hR : 0 < R)
    (hepsilon : 0 ≤ epsilon) (t z w : ℝ) :
    |slowTimeCutoff R epsilon t z - slowTimeCutoff R epsilon t w| ≤
      (epsilon / R) * |z - w| := by
  have hratio : 0 ≤ epsilon / R := div_nonneg hepsilon hR.le
  have hm := abs_min_sub_min_le_max t ((epsilon / R) * (R - |z|))
    t ((epsilon / R) * (R - |w|))
  have hn : 0 ≤ |(epsilon / R) * (R - |z|) - (epsilon / R) * (R - |w|)| :=
    abs_nonneg _
  simp only [sub_self, abs_zero, max_eq_right hn] at hm
  have heq : (epsilon / R) * (R - |z|) - (epsilon / R) * (R - |w|) =
      (epsilon / R) * (|w| - |z|) := by ring
  rw [heq, abs_mul, abs_of_nonneg hratio] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (by simpa only [abs_sub_comm w z] using abs_abs_sub_abs_le_abs_sub w z) hratio)

theorem injOn_transverse_cutoff {Q : Type*} (F : Q × (ℝ × ℝ) → E)
    (B : Set Q) (I J : Set ℝ) (v : E) (g : ℝ → ℝ)
    (hF : InjOn F (B ×ˢ (I ×ˢ J)))
    {L k : ℝ} (hL : 0 ≤ L)
    (htrans : ∀ x ∈ B ×ˢ (I ×ˢ J), ∀ y ∈ B ×ˢ (I ×ˢ J),
      |x.2.2 - y.2.2| ≤ L * ‖F x - F y‖)
    (hg : MapsTo g J I)
    (hslow : ∀ z ∈ J, ∀ w ∈ J, |g z - g w| ≤ k * |z - w|)
    (hsmall : L * ‖v‖ * k < 1) :
    InjOn (fun p : Q × ℝ => F (p.1, (g p.2, p.2)) - g p.2 • v)
      (B ×ˢ J) := by
  rintro ⟨p, z⟩ hp ⟨q, w⟩ hq heq
  have hp' : (p, (g z, z)) ∈ B ×ˢ (I ×ˢ J) := ⟨hp.1, hg hp.2, hp.2⟩
  have hq' : (q, (g w, w)) ∈ B ×ˢ (I ×ˢ J) := ⟨hq.1, hg hq.2, hq.2⟩
  have hdiff : F (p, (g z, z)) - F (q, (g w, w)) = (g z - g w) • v := by
    change F (p, (g z, z)) - g z • v = F (q, (g w, w)) - g w • v at heq
    rw [sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp heq
  have hzbound := htrans _ hp' _ hq'
  change |z - w| ≤ L * ‖F (p, (g z, z)) - F (q, (g w, w))‖ at hzbound
  rw [hdiff, norm_smul, Real.norm_eq_abs] at hzbound
  have hbound : |z - w| ≤ (L * ‖v‖ * k) * |z - w| := by
    calc
      |z - w| ≤ L * (|g z - g w| * ‖v‖) := hzbound
      _ ≤ L * ((k * |z - w|) * ‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hslow z hp.2 w hq.2) (norm_nonneg v)) hL
      _ = (L * ‖v‖ * k) * |z - w| := by ring
  have hzw : z = w := by
    have hzero : |z - w| = 0 := by nlinarith [abs_nonneg (z - w)]
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  subst w
  have hvalue : F (p, (g z, z)) = F (q, (g z, z)) := by
    simpa only [sub_add_cancel] using congrArg (fun x : E => x + g z • v) heq
  have hfull : (p, (g z, z)) = (q, (g z, z)) := hF hp' hq' hvalue
  have hpq : p = q := congrArg (fun u : Q × (ℝ × ℝ) => u.1) hfull
  exact congrArg (fun u : Q => (u, z)) hpq

end PoincareConjecture.M76.ZeroChargeJoint
