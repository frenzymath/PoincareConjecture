import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Pullback
import Mathlib.Geometry.Manifold.IntegralCurve.Basic










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle Metric
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

private theorem exists_smooth_local_timeDependent_euclidean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set (ℝ × E)} (hU : IsOpen U) {F : ℝ → E → E}
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) U) {s : ℝ} {x₀ : E}
    (hx₀ : (s, x₀) ∈ U) :
    ∃ (V : Set E) (δ : ℝ) (Φ : E × ℝ → E),
      IsOpen V ∧ x₀ ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (s - δ) (s + δ)) ∧
      (∀ x ∈ V, Φ (x, s) = x) ∧
      (∀ x ∈ V, ∀ t ∈ Ioo (s - δ) (s + δ), (t, Φ (x, t)) ∈ U) ∧
      (∀ x ∈ V, ∀ t ∈ Ioo (s - δ) (s + δ),
        HasDerivAt (fun r => Φ (x, r)) (F t (Φ (x, t))) t) := by
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx₀)
  let χ : ContDiffBump (s, x₀) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  let G : ℝ × E → E := fun p => χ p • F p.1 p.2
  have hχU : tsupport (χ : ℝ × E → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact hdU
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport (χ : ℝ × E → ℝ)
    · exact χ.contDiff.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds (hχU hp)))
    · have heq : G =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
        filter_upwards [(isClosed_tsupport (χ : ℝ × E → ℝ)).isOpen_compl.mem_nhds hp]
          with y hy
        change χ y • F y.1 y.2 = 0
        rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hGF : EqOn G (Function.uncurry F) (ball (s, x₀) (d / 2)) := by
    intro p hp
    change χ p • F p.1 p.2 = F p.1 p.2
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hp), one_smul]
  obtain ⟨r, ε, hr, hε, Φ, hΦ, ρ, T, hρ, hT, hρr, hTε, hSmooth⟩ :=
    Poincare.ODE.LocalFlow.exists_isLocalFlow_contDiffOn_top
      (f := fun t x => G (t, x)) (t₀ := s) (x₀ := x₀) hG
  let D : Set (E × ℝ) := ball x₀ ρ ×ˢ Ioo (s - T) (s + T)
  let W : Set (E × ℝ) := D ∩ (fun q => (q.2, Φ q)) ⁻¹' ball (s, x₀) (d / 2)
  have hWopen : IsOpen W :=
    (continuousOn_snd.prodMk hSmooth.continuousOn).isOpen_inter_preimage
      (isOpen_ball.prod isOpen_Ioo) isOpen_ball
  have hWmem : (x₀, s) ∈ W := by
    refine ⟨⟨mem_ball_self hρ, ⟨by linarith, by linarith⟩⟩, ?_⟩
    change (s, Φ (x₀, s)) ∈ ball (s, x₀) (d / 2)
    rw [hΦ.apply_initial x₀ (mem_closedBall_self hr.le)]
    exact mem_ball_self (half_pos hd)
  obtain ⟨a, ha, haW⟩ := Metric.isOpen_iff.mp hWopen (x₀, s) hWmem
  have hsub : ball x₀ a ×ˢ Ioo (s - a) (s + a) ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    apply haW
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
    exact ⟨hx, abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hinit : ∀ x ∈ ball x₀ a, Φ (x, s) = x := by
    intro x hx
    have hxρ := (hsub (show (x, s) ∈ _ from ⟨hx, ⟨by linarith, by linarith⟩⟩)).1.1
    exact hΦ.apply_initial x (ball_subset_closedBall (ball_subset_ball hρr hxρ))
  refine ⟨ball x₀ a, a, Φ, isOpen_ball, mem_ball_self ha, ha,
    hSmooth.mono (fun q hq => (hsub hq).1), hinit, ?_, ?_⟩
  · intro x hx t ht
    exact hdU (closedBall_subset_closedBall (by linarith)
      (ball_subset_closedBall (hsub (show (x, t) ∈ _ from ⟨hx, ht⟩)).2))
  · intro x hx t ht
    have hq := hsub (show (x, t) ∈ _ from ⟨hx, ht⟩)
    have htε : t ∈ Ioo (s - ε) (s + ε) :=
      ⟨by linarith [hq.1.2.1], by linarith [hq.1.2.2]⟩
    have hderiv := hΦ.hasDerivWithinAt x
      (ball_subset_closedBall (ball_subset_ball hρr hq.1.1)) t
      (Ioo_subset_Icc_self htε)
    have hderiv' := hderiv.hasDerivAt (Icc_mem_nhds htε.1 htε.2)
    rw [show G (t, Φ (x, t)) = F t (Φ (x, t)) from hGF hq.2] at hderiv'
    exact hderiv'

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_smooth_local_timeDependentFlow
    {J : Set ℝ} (hJ : IsOpen J)
    {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {s : ℝ} (hs : s ∈ J) (p : M) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ p ∈ V ∧ 0 < δ ∧ Ioo (s - δ) (s + δ) ⊆ J ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (s - δ) (s + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (s, y) = y) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (s - δ) (s + δ),
        HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => Φ (r, y)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ (t, y)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    simpa only [c, extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := p) (n := ∞))
  have hc (y : M) (hy : y ∈ c.source) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y :=
    hchart.contMDiffAt (extChartAt_source_mem_nhds' hy)
  have hci (z : E) (hz : z ∈ c.target) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  let F : ℝ → E → E := fun t z =>
    mfderiv (𝓡 n) (𝓡 n) c (c.symm z) (X t (c.symm z))
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (J ×ˢ c.target) := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun q : ℝ × E => c.symm q.2) (t, z) :=
      (hci z hz).comp (t, z) contMDiffAt_snd
    have hparam : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun q : ℝ × E => (q.1, c.symm q.2)) (t, z) :=
      contMDiffAt_fst.prodMk hbase
    have hX' := (hX.contMDiffAt
      ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).comp (t, z) hparam
    have hmf := ((hc _ (c.map_target hz)).mfderiv_const (m := ∞) (by simp)).comp
      (t, z) hbase
    have hd := hmf.clm_apply_of_inCoordinates hX'
      ((hc _ (c.map_target hz)).comp (t, z) hbase)
    have hcoord := (contMDiff_snd_tangentBundle_modelSpace E (𝓡 n)).contMDiffAt.comp _ hd
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hcoord
    exact hcoord.contDiffAt.contDiffWithinAt
  have hpush (t : ℝ) (z : E) (hz : z ∈ c.target) :
      mfderiv (𝓡 n) (𝓡 n) c.symm z (F t z) = X t (c.symm z) := by
    have h := congrArg (fun L => L (X t (c.symm z)))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n)
        (c.map_target hz))
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ,
      ContinuousLinearMap.comp_apply] at h
    change mfderiv (𝓡 n) (𝓡 n) c.symm (c (c.symm z)) (F t z) =
      X t (c.symm z) at h
    rw [c.right_inv hz] at h
    exact h
  obtain ⟨B, δ, q, hB, hpB, hδ, hq, hq0, hqmem, hqtime⟩ :=
    exists_smooth_local_timeDependent_euclidean (hJ.prod (isOpen_extChartAt_target p))
      hF (show (s, c p) ∈ J ×ˢ c.target from ⟨hs, mem_extChartAt_target p⟩)
  let V := c.source ∩ c ⁻¹' B
  have hV : IsOpen V :=
    hchart.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_source p) hB
  let Φ : ℝ × M → M := fun z => c.symm (q (c z.2, z.1))
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
      (Ioo (s - δ) (s + δ) ×ˢ V) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ (fun z : ℝ × M => (c z.2, z.1)) (t, y) :=
      ((hc y hy.1).comp (t, y) contMDiffAt_snd).prodMk contMDiffAt_fst
    have hqm : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞ q (c y, t) := by
      have hqd := hq.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds
        (show (c y, t) ∈ B ×ˢ Ioo (s - δ) (s + δ) from ⟨hy.2, ht⟩))
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hqd.contMDiffAt
    exact ((hci _ (hqmem _ hy.2 t ht).2).comp (t, y)
      (hqm.comp (t, y) hp)).contMDiffWithinAt
  refine ⟨V, δ, Φ, hV, ⟨mem_extChartAt_source p, hpB⟩, hδ,
    (fun t ht => (hqmem _ hpB t ht).1), hΦ, ?_, ?_⟩
  · intro y hy
    change c.symm (q (c y, s)) = y
    rw [hq0 _ hy.2, c.left_inv hy.1]
  · intro y hy t ht
    have hd := ((hci _ (hqmem _ hy.2 t ht).2).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
      (hqtime _ hy.2 t ht).hasFDerivAt.hasMFDerivAt
    apply hd.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv (𝓡 n) (𝓡 n) c.symm (q (c y, t)) (a • F t (q (c y, t))) =
      a • X t (c.symm (q (c y, t)))
    rw [map_smul, hpush _ _ (hqmem _ hy.2 t ht).2]

end Poincare.Manifold
