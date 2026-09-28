import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.TailTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Euclidean.Triangular
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)

theorem exists_small_time_cutoff {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ ∃ θ : Real → Real, ContDiff Real ∞ θ ∧
      (∀ t, θ t ∈ Ioo (-ε) ε) ∧ ∀ t ∈ Icc (-r) r, θ t = t := by
  let χ : ContDiffBump (0 : Real) :=
    { rIn := ε / 4, rOut := ε / 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  refine ⟨ε / 4, by positivity, fun t => χ t * t,
    χ.contDiff.mul contDiff_id, ?_, ?_⟩
  · intro t
    apply abs_lt.mp
    by_cases ht : |t| < ε / 2
    · rw [abs_mul, abs_of_nonneg χ.nonneg]
      calc
        χ t * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
        _ < ε := by simpa using ht.trans (by linarith : ε / 2 < ε)
    · have hz : χ t = 0 := χ.zero_of_le_dist (by
        simpa only [Real.dist_eq, sub_zero] using le_of_not_gt ht)
      simpa only [hz, zero_mul, abs_zero] using hε
  · intro t ht
    change χ t * t = t
    rw [χ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht), one_mul]



theorem exists_cutoff_parameter_family
    (α : Real × Real → Real) (hα : ContDiff Real ∞ α)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hzero : ∀ s ∈ tsupport χ, α (0, s) = s) :
    ∃ r : Real, 0 < r ∧ ∃ R : Real → Real ≃ₘ[Real] Real,
      (∀ s, R 0 s = s) ∧
      ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
      (∀ t s, s ∉ tsupport χ → R t s = s) ∧
      ∀ t ∈ Icc (-r) r, ∀ s, R t s = s + χ s * (α (t, s) - s) := by
  let F : Real × Real → Real := fun z => z.2 + χ z.2 * (α z - z.2)
  have hF : ContDiff Real ∞ F :=
    contDiff_snd.add ((hχ.comp contDiff_snd).mul (hα.sub contDiff_snd))
  have hFzero : (fun s => F (0, s)) = id := by
    funext s
    by_cases hs : s ∈ tsupport χ
    · simp [F, hzero s hs]
    · simp [F, image_eq_zero_of_notMem_tsupport hs]
  let dF : Real × Real → Real := fun z => deriv (fun s => F (z.1, s)) z.2
  have hdF : ContDiff Real ∞ dF := by
    have hA : ContDiff Real ∞ (fun z : Real × Real =>
        fderiv Real (fun s => F (z.1, s)) z.2) :=
      (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv contDiff_snd (by simp)
    exact hA.clm_apply contDiff_const
  have hdFzero (s : Real) : dF (0, s) = 1 := by
    change deriv (fun s => F (0, s)) s = 1
    rw [hFzero, deriv_id]
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, 0 < dF (t, s) := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hdF.continuous.continuousAt.eventually
      (Ioi_mem_nhds (by rw [hdFzero]; norm_num))
  obtain ⟨ε, hε, hεd⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨r, hr, θ, hθ, hθrange, hθid⟩ := exists_small_time_cutoff hε
  let G : Real × Real → Real := fun z => F (θ z.1, z.2)
  have hG : ContDiff Real ∞ G := hF.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)
  have hGfix (t s : Real) (hs : s ∉ tsupport χ) : G (t, s) = s := by
    simp [G, F, image_eq_zero_of_notMem_tsupport hs]
  have hGder (t s : Real) : 0 < deriv (fun y => G (t, y)) s := by
    by_cases hs : s ∈ tsupport χ
    · apply hεd (show θ t ∈ ball (0 : Real) ε from ?_) s hs
      simpa only [mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr (hθrange t)
    · have heq : (fun y => G (t, y)) =ᶠ[𝓝 s] id := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hs] with y hy
        exact hGfix t y hy
      rw [heq.deriv_eq, deriv_id]
      norm_num
  have hGbound (t : Real) : ∃ C : Real, ∀ s, |G (t, s) - s| ≤ C := by
    obtain ⟨B, hB⟩ := hχc.isCompact.exists_bound_of_continuousOn
      ((hG.continuous.comp (continuous_const.prodMk continuous_id)).sub continuous_id).continuousOn
    refine ⟨max B 0, ?_⟩
    intro s
    by_cases hs : s ∈ tsupport χ
    · exact (hB s hs).trans (le_max_left _ _)
    · rw [hGfix t s hs, sub_self, abs_zero]
      exact le_max_right _ _
  have hbij (t : Real) : Bijective (fun s => G (t, s)) :=
    Poincare.Manifold.bijective_of_deriv_pos_of_bounded_displacement
      (hG.continuous.comp (continuous_const.prodMk continuous_id)) (hGder t) (hGbound t)
  obtain ⟨g, hg, hright, hleft⟩ :=
    Poincare.Manifold.exists_smooth_scalar_inverse hG hbij (fun t s => (hGder t s).ne')
  let R (t : Real) : Real ≃ₘ[Real] Real :=
    { toEquiv := {
        toFun := fun s => G (t, s)
        invFun := fun s => g (t, s)
        left_inv := hleft t
        right_inv := hright t }
      contMDiff_toFun := (hG.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hg.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨r, hr, R, ?_, hG, hg, hGfix, ?_⟩
  · intro s
    change F (θ 0, s) = s
    rw [hθid 0 ⟨by linarith, hr.le⟩]
    exact congrFun hFzero s
  · intro t ht s
    change F (θ t, s) = _
    rw [hθid t ht]



theorem exists_cutoff_parameter_family_on
    (α : Real × Real → Real) {W : Set (Real × Real)} (hW : IsOpen W)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hWzero : ∀ s ∈ tsupport χ, (0, s) ∈ W)
    (hα : ContDiffOn Real ∞ α W)
    (hzero : ∀ s ∈ tsupport χ, α (0, s) = s) :
    ∃ r : Real, 0 < r ∧ ∃ R : Real → Real ≃ₘ[Real] Real,
      (∀ s, R 0 s = s) ∧
      ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
      (∀ t s, s ∉ tsupport χ → R t s = s) ∧
      ∀ t ∈ Icc (-r) r, ∀ s, R t s = s + χ s * (α (t, s) - s) := by
  have hK : IsCompact (({0} : Set Real) ×ˢ tsupport χ) :=
    isCompact_singleton.prod hχc.isCompact
  have hKW : ({0} : Set Real) ×ˢ tsupport χ ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht0 : t = 0 := ht
    subst t
    exact hWzero s hs
  obtain ⟨β, hβ, _, hβα⟩ :=
    Poincare.Parabolic.Interior.exists_compact_smooth_extension hK hW hKW hα
  have hβzero (s : Real) (hs : s ∈ tsupport χ) : β (0, s) = s :=
    ((hβα (0, s) ⟨rfl, hs⟩).self_of_nhds).trans (hzero s hs)
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, β (t, s) = α (t, s) := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hβα (0, s) ⟨rfl, hs⟩
  obtain ⟨ε, hε, hεeq⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRformula⟩ :=
    exists_cutoff_parameter_family β hβ χ hχ hχc hβzero
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  refine ⟨δ, hδ, R, hRzero, hR, hRinv, hRfix, ?_⟩
  intro t ht s
  have htr : t ∈ Icc (-r) r := by
    have hd := min_le_left r (ε / 2)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hRformula t htr s]
  by_cases hs : s ∈ tsupport χ
  · have htε : t ∈ ball (0 : Real) ε := by
      have hd := min_le_right r (ε / 2)
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hεeq htε s hs]
  · simp only [image_eq_zero_of_notMem_tsupport hs, zero_mul]



theorem exists_strip_tail_parameter_family
    {height : S2 → Real} {c : Real}
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ u ∈ e.source, height (e u) = c - (u 0)^2 + (u 1)^2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hK : ∀ s ∈ tsupport χ, (s, 0) ∈ F.source ∧ F (s, 0) ∈ e.target ∧
      e.symm (F (s, 0)) 0 < 0) :
    ∃ r : Real, 0 < r ∧ ∃ R : Real → Real ≃ₘ[Real] Real,
      (∀ s, R 0 s = s) ∧
      ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
      (∀ t s, s ∉ tsupport χ → R t s = s) ∧
      ∀ t ∈ Icc (-r) r, ∀ s, χ s = 1 →
        (R t s, t) ∈ F.source ∧
        F (R t s, t) = rawTailPoint e F (t, s) ∧
        e.symm (F (R t s, t)) 1 = tailCoordinate e F s := by
  obtain ⟨W, hW, hKW, hq, hqt, hqh, hqy, _, _, _, hqzero⟩ :=
    exists_raw_tail_transport_neighborhood e he hei hform F hF hheight (tsupport χ) hK
  let α : Real × Real → Real := fun z => (F.symm (rawTailPoint e F z)).1
  have hα : ContDiffOn Real ∞ α W := (hFi.comp hq hqt).contDiffOn.fst
  have hαzero (s : Real) (hs : s ∈ tsupport χ) : α (0, s) = s := by
    dsimp [α]
    rw [hqzero s hs, F.left_inv (hK s hs).1]
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRformula⟩ :=
    exists_cutoff_parameter_family_on α hW χ hχ hχc
      (fun s hs => hKW ⟨rfl, hs⟩) hα hαzero
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, (t, s) ∈ W := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hW.mem_nhds (hKW ⟨rfl, hs⟩)
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hevent
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  refine ⟨δ, hδ, R, hRzero, hR, hRinv, hRfix, ?_⟩
  intro t ht s hs
  have htr : t ∈ Icc (-r) r := by
    have hd := min_le_left r (ε / 2)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htε : t ∈ ball (0 : Real) ε := by
    have hd := min_le_right r (ε / 2)
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsK : s ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hs])
  have hts := hεW htε s hsK
  have hback := F.right_inv (hqt hts)
  have hsrc := F.map_target (hqt hts)
  have hcoordheight := hheight _ hsrc
  rw [hback, hqh (t, s) hts] at hcoordheight
  have hcoord : (F.symm (rawTailPoint e F (t, s))).2 = t := by linarith
  have hpair : (α (t, s), t) = F.symm (rawTailPoint e F (t, s)) :=
    Prod.ext rfl hcoord.symm
  have hRα : R t s = α (t, s) := by
    rw [hRformula t htr s, hs, one_mul, add_sub_cancel]
  rw [hRα, hpair]
  refine ⟨hsrc, hback, ?_⟩
  rw [hback]
  exact hqy (t, s) hts

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
