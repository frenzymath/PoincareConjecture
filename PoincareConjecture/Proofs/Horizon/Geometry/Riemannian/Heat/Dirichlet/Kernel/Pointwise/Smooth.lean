import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Time
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

omit [NeZero n] [MeasurableSpace M] [BorelSpace M] [T3Space M] in
private theorem contMDiffOn_of_inner_smooth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {F : M → H} (hU : IsOpen Ω) (hFc : ContinuousOn F Ω)
    (hF : ∀ v : H, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => inner ℝ (F x) v) Ω) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, H) ∞ F Ω := by
  apply contMDiffOn_iff.mpr
  refine ⟨hFc, ?_⟩
  intro x y
  simp only [mfld_simps]
  apply Poincare.Analysis.contDiffOn_of_inner_smooth
  · exact (chartAt (EuclideanSpace ℝ (Fin n)) x).isOpen_inter_preimage_symm hU
  · intro v
    have h := (contMDiffOn_iff.mp (hF v)).2 x (0 : ℝ)
    simpa only [mfld_simps, Function.comp_def] using h

variable (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

theorem contMDiffOn_evaluationRow_heatPowerContinuous (k : ℕ) (t : ℝ) (ht : 0 < t) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, Lp ℝ 2 (g.volumeMeasure.restrict Ω)) ∞
      (evaluationRow (heatPowerContinuous D S k t ht)) Ω := by
  apply contMDiffOn_of_inner_smooth S.isOpen
  · exact (continuous_evaluationRow _
      (isCompactOperator_heatPowerContinuous D S k t ht)).continuousOn
  · intro f
    simpa only [inner_evaluationRow] using contMDiffOn_heatPowerContinuous D S k t ht f

private theorem contDiffOn_heatSpectralPower_operator (k : ℕ) :
    ContDiffOn ℝ ∞
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k) (Ioi 0) := by
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure
  have hder (j : ℕ) {t : ℝ} (ht : 0 < t) :
      HasDerivAt (P j) (-P (j + 1) t) t :=
    Poincare.Analysis.Dirichlet.Spectral.hasDerivAt_heatPower
      (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
      (eigenvalueNN D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure) j ht
  have hall : ∀ m : ℕ, ∀ j : ℕ, ContDiffOn ℝ m (P j) (Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro j
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht => (hder j ht).continuousAt.continuousWithinAt
    | succ m ih =>
      intro j
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht => (hder j ht).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      exact (ih (j + 1)).neg.congr (fun t ht => (hder j ht).deriv)
  exact contDiffOn_infty.mpr (fun m => hall m k)

private theorem evaluationRow_add_power (k : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x : M) :
    evaluationRow (heatPowerContinuous D S k (s + t) (add_pos hs ht)) x =
      heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 t
        (evaluationRow (heatPowerContinuous D S k s hs) x) := by
  rw [heatSpectralPower_zero_eq_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure ht]
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationRow, heatPowerContinuous_add_comp D S k s t hs ht]
  rw [(heatSemigroup_isSelfAdjoint D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure t.toNNReal).isSymmetric.apply_clm]
  exact (inner_evaluationRow (heatPowerContinuous D S k s hs) x _).symm

private theorem contMDiffAt_evaluationRow_heatPowerContinuousTime (k : ℕ)
    (p : M × ℝ) (hx : p.1 ∈ Ω) (ht : 0 < p.2) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Lp ℝ 2 (g.volumeMeasure.restrict Ω)) ∞
      (fun q : M × ℝ => evaluationRow (heatPowerContinuousTime D S k q.2) q.1) p := by
  let a : ℝ := p.2 / 2
  have ha : 0 < a := half_pos ht
  have hat : a < p.2 := half_lt_self ht
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure 0
  let r := evaluationRow (heatPowerContinuous D S k a ha)
  have hP : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ]
        Lp ℝ 2 (g.volumeMeasure.restrict Ω)) ∞
      (fun q : M × ℝ => P (q.2 - a)) p := by
    have hPa : ContDiffAt ℝ ∞ P (p.2 - a) :=
      (contDiffOn_heatSpectralPower_operator D S 0).contDiffAt
        (isOpen_Ioi.mem_nhds (sub_pos.mpr hat))
    exact hPa.contMDiffAt.comp p
      ((contDiff_id.sub (contDiff_const (c := a))).contMDiff.contMDiffAt.comp p
        contMDiffAt_snd)
  have hr : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Lp ℝ 2 (g.volumeMeasure.restrict Ω)) ∞ (fun q : M × ℝ => r q.1) p :=
    (contMDiffOn_evaluationRow_heatPowerContinuous D S k a ha).contMDiffAt
      (S.isOpen.mem_nhds hx) |>.comp p contMDiffAt_fst
  have heq : (fun q : M × ℝ => evaluationRow (heatPowerContinuousTime D S k q.2) q.1)
      =ᶠ[𝓝 p] (fun q : M × ℝ => P (q.2 - a) (r q.1)) := by
    filter_upwards [(continuous_snd.tendsto p) (Ioi_mem_nhds hat)] with q hq
    have hqa : 0 < q.2 - a := sub_pos.mpr hq
    have hsum : a + (q.2 - a) = q.2 := by ring
    have hqpos : 0 < q.2 := ha.trans hq
    rw [heatPowerContinuousTime_of_pos D S k hqpos]
    have h := evaluationRow_add_power D S k a (q.2 - a) ha hqa q.1
    simpa only [hsum, P, r] using h
  exact (hP.clm_apply hr).congr_of_eventuallyEq heq

theorem contMDiffOn_heatKernelContinuousTime_joint :
    ContMDiffOn (((𝓡 n).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : (M × M) × ℝ => heatKernelContinuousTime D S p.2 p.1.1 p.1.2)
      ((Ω ×ˢ Ω) ×ˢ Ioi 0) := by
  intro p hp
  have htime : ContMDiffAt (((𝓡 n).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (M × M) × ℝ => q.2 / 2) p :=
    (contDiff_id.div_const (2 : ℝ)).contMDiff.contMDiffAt.comp p contMDiffAt_snd
  have hleft : ContMDiffAt (((𝓡 n).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun q : (M × M) × ℝ => q.1.1) p := contMDiffAt_fst.fst
  have hright : ContMDiffAt (((𝓡 n).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun q : (M × M) × ℝ => q.1.2) p := contMDiffAt_fst.snd
  have hx := (contMDiffAt_evaluationRow_heatPowerContinuousTime D S 0
    (p.1.1, p.2 / 2) hp.1.1 (half_pos hp.2)).comp p (hleft.prodMk htime)
  have hy := (contMDiffAt_evaluationRow_heatPowerContinuousTime D S 0
    (p.1.2, p.2 / 2) hp.1.2 (half_pos hp.2)).comp p (hright.prodMk htime)
  exact (contDiff_inner.contMDiff.contMDiffAt.comp p (hx.prodMk_space hy)).contMDiffWithinAt

end PoincareConjecture.LeviCivitaData.Dirichlet
