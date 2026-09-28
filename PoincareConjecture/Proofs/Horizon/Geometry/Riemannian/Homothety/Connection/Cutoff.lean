import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Scaling
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Homothety

theorem exists_smooth_euclidean_cutoff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : E) (R : ℝ) (hR : 0 < R) :
    ∃ b : E → ℝ, ContDiff ℝ ∞ b ∧ Function.support b ⊆ Metric.closedBall c R ∧
      b =ᶠ[nhds c] (fun _ ↦ 1) := by
  let phi : E → ℝ := fun y ↦ 2 - 2 * ‖y - c‖ ^ 2 / R ^ 2
  have hnorm : ContDiff ℝ ∞ (fun y : E ↦ ‖y - c‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hphi : ContDiff ℝ ∞ phi :=
    contDiff_const.sub ((contDiff_const.mul hnorm).div_const _)
  refine ⟨Real.smoothTransition ∘ phi, Real.smoothTransition.contDiff.comp hphi, ?_, ?_⟩
  · intro y hy
    have hpos : 0 < phi y := lt_of_not_ge fun h ↦ hy (Real.smoothTransition.zero_of_nonpos h)
    have hsmall : 2 * ‖y - c‖ ^ 2 < 2 * R ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hR)).mp (sub_pos.mp hpos)
    change dist y c ≤ R
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (y - c)]
  · have hnear : ∀ᶠ y in nhds c, 1 ≤ phi y :=
      hphi.continuous.continuousAt.eventually (le_mem_nhds (by simp [phi]))
    exact hnear.mono fun _ hy ↦ Real.smoothTransition.one_of_one_le hy

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M]

theorem exists_smooth_cutoff (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ b : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ) ∞ b ∧ tsupport b ⊆ U ∧
      b =ᶠ[nhds x] (fun _ ↦ 1) := by
  classical
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxsource : x ∈ e.source := ChartedSpace.mem_chart_source x
  have hneigh : e.target ∩ e.symm ⁻¹' U ∈ nhds (e x) :=
    (e.isOpen_inter_preimage_symm hU).mem_nhds
      ⟨e.map_source hxsource, by change e.symm (e x) ∈ U; rwa [e.left_inv hxsource]⟩
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hneigh
  obtain ⟨b0, hb0, hsupp0, hnear0⟩ := exists_smooth_euclidean_cutoff (e x) R hR
  let b : M → ℝ := e.source.indicator (b0 ∘ e)
  let K := e.symm '' Metric.closedBall (e x) R
  have hKcompact : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (e.symm.continuousOn.mono (fun _ hp ↦ (hball hp).1))
  have hKsource : K ⊆ e.source := by
    rintro p ⟨y, hy, rfl⟩
    exact e.map_target (hball hy).1
  have hKU : K ⊆ U := by
    rintro p ⟨y, hy, rfl⟩
    exact (hball hy).2
  have hsupp : Function.support b ⊆ K := by
    intro p hp
    change b p ≠ 0 at hp
    have hps : p ∈ e.source := by
      by_contra hps
      exact hp (Set.indicator_of_notMem hps _)
    have hp0 : b0 (e p) ≠ 0 := by
      simpa only [b, Set.indicator_of_mem hps, Function.comp_apply] using hp
    exact ⟨e p, hsupp0 hp0, e.left_inv hps⟩
  have htsupp : tsupport b ⊆ K := closure_minimal hsupp hKcompact.isClosed
  have heq {p : M} (hp : p ∈ e.source) : b =ᶠ[nhds p] b0 ∘ e :=
    Set.eqOn_indicator.eventuallyEq_of_mem (e.open_source.mem_nhds hp)
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ b := by
    apply contMDiff_of_tsupport
    intro p hp
    have hps := hKsource (htsupp hp)
    have he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e p :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hps
    exact (hb0.contDiffAt.contMDiffAt.comp p he).congr_of_eventuallyEq (heq hps)
  refine ⟨b, hb, htsupp.trans hKU, ?_⟩
  exact (heq hxsource).trans (hnear0.comp_tendsto (e.continuousAt hxsource))

end PoincareConjecture.Homothety
