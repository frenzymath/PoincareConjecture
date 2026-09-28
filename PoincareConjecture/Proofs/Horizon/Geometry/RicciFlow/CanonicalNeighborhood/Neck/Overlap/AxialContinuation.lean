import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem axial_segment_contained_of_signed_deriv_bounds
    (N P : EpsilonNeck g) (q : UnitTwoSphere) {t₀ v L s₀ lo hi : ℝ}
    (hdom : ∀ s ∈ Icc 0 L, t₀ + v * s ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹)
    (hstart : P.coordinate_map (q, t₀) ∈ N.carrier)
    (hs₀ : (N.coordinate_inverse (P.coordinate_map (q, t₀))).2 = s₀)
    (hderiv : ∀ s ∈ Icc 0 L,
      MapsTo (fun r => P.coordinate_map (q, t₀ + v * r)) (Icc 0 s) N.carrier →
        lo ≤ v * deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2)
          (t₀ + v * s) ∧
        v * deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2)
          (t₀ + v * s) ≤ hi)
    (hlower : -N.epsilon⁻¹ < min s₀ (s₀ + lo * L))
    (hupper : max s₀ (s₀ + hi * L) < N.epsilon⁻¹) :
    MapsTo (fun s => P.coordinate_map (q, t₀ + v * s)) (Icc 0 L) N.carrier ∧
      ∀ s ∈ Icc 0 L,
        s₀ + lo * s ≤ (N.coordinate_inverse (P.coordinate_map (q, t₀ + v * s))).2 ∧
        (N.coordinate_inverse (P.coordinate_map (q, t₀ + v * s))).2 ≤ s₀ + hi * s := by
  let f : ℝ → ℝ := fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2
  let γ : ℝ → M := fun s => P.coordinate_map (q, t₀ + v * s)
  let F : ℝ → ℝ := fun s => f (t₀ + v * s)
  have hF₀ : F 0 = s₀ := by simpa [F, f] using hs₀
  have hγ : ContinuousOn γ (Icc 0 L) := by
    apply P.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk (continuous_const.add
        (continuous_const.mul continuous_id))).continuousOn
    intro s hs
    exact ⟨mem_univ _, hdom s hs⟩
  have hlocal (t : ℝ) (ht : t ∈ Icc 0 L)
      (hcarrier : MapsTo γ (Icc 0 t) N.carrier) :
      s₀ + lo * t ≤ F t ∧ F t ≤ s₀ + hi * t := by
    have hsub : Icc 0 t ⊆ Icc 0 L := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
    have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
        HasDerivAt F (v * deriv f (t₀ + v * s)) s := by
      have hf : HasDerivAt f (deriv f (t₀ + v * s)) (t₀ + v * s) :=
        ((N.transition_axis_contDiffAt P q (hdom s (hsub hs))
          (hcarrier hs)).differentiableAt (by simp)).hasDerivAt
      have ha : HasDerivAt (fun r : ℝ => t₀ + v * r) v s := by
        simpa using ((hasDerivAt_id s).const_mul v).const_add t₀
      have hcomp := hf.comp s ha
      change HasDerivAt F (deriv f (t₀ + v * s) * v) s at hcomp
      rw [mul_comm (deriv f (t₀ + v * s)) v] at hcomp
      exact hcomp
    rcases ht.1.eq_or_lt with rfl | hpos
    · simp [hF₀]
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope F hpos
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt)
    have hprefix : MapsTo γ (Icc 0 c) N.carrier :=
      fun s hs => hcarrier ⟨hs.1, hs.2.trans hc.2.le⟩
    have hb := hderiv c (hsub (Ioo_subset_Icc_self hc)) hprefix
    rw [(hd c (Ioo_subset_Icc_self hc)).deriv, hF₀, sub_zero] at heq
    have heq' := (eq_div_iff hpos.ne').mp heq
    have hlo := mul_le_mul_of_nonneg_right hb.1 ht.1
    have hhi := mul_le_mul_of_nonneg_right hb.2 ht.1
    change lo * t ≤ (v * deriv f (t₀ + v * c)) * t at hlo
    change (v * deriv f (t₀ + v * c)) * t ≤ hi * t at hhi
    rw [heq'] at hlo hhi
    constructor <;> linarith
  obtain ⟨a, haN, ha⟩ := exists_between hlower
  obtain ⟨b, hb, hbN⟩ := exists_between hupper
  have ha₀ : a < s₀ := ha.trans_le (min_le_left _ _)
  have hb₀ : s₀ < b := (le_max_left _ _).trans_lt hb
  have hslab : γ 0 ∈ N.region a b := by
    exact ⟨by simpa [γ] using hstart, by simpa [γ, hs₀] using ha₀,
      by simpa [γ, hs₀] using hb₀⟩
  have hcontain : MapsTo γ (Icc 0 L) N.carrier := by
    intro t ht
    by_contra hout
    have hout' : γ t ∉ N.coordinate_map '' (univ ×ˢ Icc a b) :=
      fun h => hout ((N.mem_coordinate_slab_iff haN hbN).mp h).1
    obtain ⟨τ, hτ, hcarrier, hface, -⟩ := N.exists_initial_segment_to_slab_boundary
      ht.1 haN hbN (hγ.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)) hslab hout'
    have hτL : τ ∈ Icc 0 L := ⟨hτ.1.le, hτ.2.trans ht.2⟩
    have hbounds := hlocal τ hτL hcarrier
    have hlo : min s₀ (s₀ + lo * L) ≤ s₀ + lo * τ := by
      rcases le_total 0 lo with hsign | hsign
      · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hsign hτL.1])
      · apply (min_le_right _ _).trans
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hsign (sub_nonneg.mpr hτL.2)]
    have hhi : s₀ + hi * τ ≤ max s₀ (s₀ + hi * L) := by
      rcases le_total 0 hi with hsign | hsign
      · exact le_trans (by nlinarith [mul_nonneg hsign (sub_nonneg.mpr hτL.2)])
          (le_max_right _ _)
      · exact le_trans (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hsign hτL.1])
          (le_max_left _ _)
    have hlow : a < F τ := ha.trans_le (hlo.trans hbounds.1)
    have hhigh : F τ < b := (hbounds.2.trans hhi).trans_lt hb
    change F τ = a ∨ F τ = b at hface
    rcases hface with hface | hface <;> linarith
  exact ⟨hcontain, fun s hs => hlocal s hs
    (fun r hr => hcontain ⟨hr.1, hr.2.trans hs.2⟩)⟩

end PoincareConjecture.EpsilonNeck
