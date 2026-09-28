import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeReversal
import Mathlib.LinearAlgebra.Dual.Lemmas



set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.OriginalTriangleCopies



theorem exists_edge_scalar_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (a b : E) (hab : a ≠ b) :
    ∃ ell : E →L[ℝ] ℝ, ell (b - a) = 1 ∧
      (∀ r : ℝ, ell (AffineMap.lineMap a b r) = ell a + r) ∧
      InjOn ell (range (AffineMap.lineMap a b : ℝ → E)) := by
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℝ (sub_ne_zero.mpr hab.symm)
  let ell : E →L[ℝ] ℝ := L.toContinuousLinearMap
  have hv : ell (b - a) = 1 := hL
  have hval (r : ℝ) : ell (AffineMap.lineMap a b r) = ell a + r := by
    rw [AffineMap.lineMap_apply_module', map_add, map_smul, hv]
    simp [add_comm]
  refine ⟨ell, hv, hval, ?_⟩
  rintro x ⟨r, rfl⟩ y ⟨s, rfl⟩ he
  rw [hval, hval] at he
  exact congrArg (AffineMap.lineMap a b) (add_left_cancel he)



theorem scalar_interval_direction_of_samples
    {f : ℝ → ℝ} {a b r s : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b)) (hi : InjOn f (Icc a b))
    (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r < s) :
    SignType.sign (f b - f a) = SignType.sign (f s - f r) := by
  rcases hc.strictMonoOn_of_injOn_Icc' hab.le hi with hm | hm
  · rw [sign_pos (sub_pos.mpr (hm (left_mem_Icc.mpr hab.le)
      (right_mem_Icc.mpr hab.le) hab)), sign_pos (sub_pos.mpr (hm hr hs hrs))]
  · rw [sign_neg (sub_neg.mpr (hm (left_mem_Icc.mpr hab.le)
      (right_mem_Icc.mpr hab.le) hab)), sign_neg (sub_neg.mpr (hm hr hs hrs))]

theorem scalar_interval_endpoint_product_neg_of_samples
    {f g : ℝ → ℝ} {a b c d r s u v : ℝ} (hab : a < b) (hcd : c < d)
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (hg : ContinuousOn g (Icc c d)) (hgi : InjOn g (Icc c d))
    (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r < s)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v)
    (hneg : (f s - f r) * (g v - g u) < 0) :
    (f b - f a) * (g d - g c) < 0 := by
  have hfsgn := scalar_interval_direction_of_samples hab hf hfi hr hs hrs
  have hgsgn := scalar_interval_direction_of_samples hcd hg hgi hu hv huv
  have hsgn : SignType.sign ((f b - f a) * (g d - g c)) = -1 := by
    rw [sign_mul, hfsgn, hgsgn, ← sign_mul, sign_neg hneg]
  exact sign_eq_neg_one_iff.mp hsgn



theorem endpoint_pair_reversal_of_local_scalar_product
    {E : Type*} (ell : E → ℝ) (f g : ℝ → E)
    {a b c d r s u v : ℝ} (hab : a < b) (hcd : c < d)
    (hf : ContinuousOn (ell ∘ f) (Icc a b)) (hfi : InjOn (ell ∘ f) (Icc a b))
    (hg : ContinuousOn (ell ∘ g) (Icc c d)) (hgi : InjOn (ell ∘ g) (Icc c d))
    (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r < s)
    (hu : u ∈ Icc c d) (hv : v ∈ Icc c d) (huv : u < v)
    (hend : ({g c, g d} : Set E) = {f a, f b})
    (hneg : (ell (f s) - ell (f r)) * (ell (g v) - ell (g u)) < 0) :
    g c = f b ∧ g d = f a := by
  have hn := scalar_interval_endpoint_product_neg_of_samples hab hcd hf hfi hg hgi
    hr hs hrs hu hv huv hneg
  rcases pair_eq_pair_iff.mp hend with ⟨h0, h1⟩ | h
  · simp only [Function.comp_apply, h0, h1] at hn
    exact (not_lt_of_ge (mul_self_nonneg (ell (f b) - ell (f a))) hn).elim
  · exact h



theorem scalar_interval_direction_of_affine_overlap
    {g : ℝ → ℝ} (h : ℝ →ᵃ[ℝ] ℝ) {a b r s q : ℝ}
    (hc : ContinuousOn g (Icc a b)) (hi : InjOn g (Icc a b))
    (heq : EqOn g h (Icc r s))
    (hq : q ∈ Ioo a b) (hq' : q ∈ Ioo r s) :
    SignType.sign (g b - g a) = SignType.sign (h s - h r) := by
  let u : ℝ := (max a r + q) / 2
  let v : ℝ := (q + min b s) / 2
  have hlo : max a r < q := max_lt hq.1 hq'.1
  have hhi : q < min b s := lt_min hq.2 hq'.2
  have hau : a ≤ u := by dsimp [u]; have := le_max_left a r; linarith
  have hru : r ≤ u := by dsimp [u]; have := le_max_right a r; linarith
  have huq : u < q := by dsimp [u]; linarith
  have hqv : q < v := by dsimp [v]; linarith
  have hvb : v ≤ b := by dsimp [v]; have := min_le_left b s; linarith
  have hvs : v ≤ s := by dsimp [v]; have := min_le_right b s; linarith
  have huv : u < v := huq.trans hqv
  have hdiff (x y : ℝ) : h y - h x = (y - x) * h.linear 1 := by
    calc
      h y - h x = h.linear (y - x) := (h.linearMap_vsub y x).symm
      _ = h.linear ((y - x) • (1 : ℝ)) := by simp
      _ = (y - x) * h.linear 1 := by rw [map_smul]; rfl
  rw [scalar_interval_direction_of_samples (hq.1.trans hq.2) hc hi
    ⟨hau, huq.le.trans hq.2.le⟩ ⟨hq.1.le.trans hqv.le, hvb⟩ huv,
    heq ⟨hq'.1.le.trans hqv.le, hvs⟩, heq ⟨hru, huq.le.trans hq'.2.le⟩,
    hdiff, hdiff, sign_mul, sign_mul, sign_pos (sub_pos.mpr huv),
    sign_pos (sub_pos.mpr (hq'.1.trans hq'.2))]

end PoincareConjecture.M76.OriginalTriangleCopies
