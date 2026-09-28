import PoincareConjecture.Proofs.M47.TerminalRegularSourceCompactness
import PoincareConjecture.Proofs.M47.TerminalRegularSourceRealization
import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalStage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private def RegularNormalStageOutput
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace E N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 M) (p0 : M) (h : RiemannianMetric 3 N) (Q : ℝ)
    (j : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞) (a Rchart rho Hbar R : ℝ) : Prop :=
  ∃ cover : TerminalSourceIndexedChartCover g p0 a Rchart rho
      (⌈RiemannianMetric.modelVolume 3 Hbar (3 * a) /
        RiemannianMetric.modelVolume 3 Hbar (min (a / 2) (rho / 4) / 2)⌉₊ + 1),
    (∀ i, ∀ z ∈ Metric.closedBall (0 : E) (2 * rho), ∀ w : E,
      (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients (cover.chart i).chart z w w ∧
        g.pullbackCoefficients (cover.chart i).chart z w w ≤ (9 / 4 : ℝ) * ‖w‖ ^ 2) ∧
    (∀ (z : M) (w w' : TangentSpace (𝓡 3) z),
      g.inner z w w' = Q * h.inner (j z)
        (mfderiv (𝓡 3) (𝓡 3) j z w) (mfderiv (𝓡 3) (𝓡 3) j z w')) ∧
    h.ball (j p0) (6 * R / Real.sqrt Q) ⊆ j.target



theorem terminalSource_regular_normal_stage
    {a R r K v A : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hr : 0 < r) (hv : 0 < v)
    (haR : a ≤ R) (har : a + r ≤ R) (hlarge : 6 * R ≤ A) :
    let L : ℝ := max 1 (9 * K)
    let Hbar : ℝ := 13 * max (4 * L / 3) 1
    let Rchart : ℝ := RiemannianMetric.localInjectivityRadius 3 Hbar R v
    ∃ rho : ℝ, 0 < rho ∧ 2 * rho < Rchart ∧
      (∀ s : ℝ, |s| ≤ 2 * rho →
        (Hbar * s ^ 2) * Real.exp (max 1 (Hbar * s ^ 2)) ≤ 3) ∧
      ∀ {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
        (H : M33RegularHistoryData W) (base tau0 tau : ℝ)
        (hbase : base ∈ H.generalized.interval) (_htau0 : 0 < tau0) (htau : 0 < tau)
        (x : (H.generalized.slice base).carrier),
      let Q : ℝ := H.generalized.scalar ⟨base, x⟩
      let U : TopologicalSpace.Opens (F.slice base).carrier :=
        ⟨(F.metric base).ball (H.history.forward base hbase x) (A / Real.sqrt Q),
          M04.initial_ball_isOpen _ _ _⟩
      ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau0) 0) U,
      (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) →
      ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤ calibratedMetricVolume
        (H.generalized.metric base) ((H.generalized.metric base).ball x (r / Real.sqrt Q)) →
      ∀ (p0 : U), p0.val = H.history.forward base hbase x →
      ∀ (htime : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval)
        (d : GeneralizedFlowCylinder H.generalized (F.slice base) base Q (Icc (-tau) 0) U)
        (G : RicciFlow 3 U (Icc (-tau) 0)),
      let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
      (∀ (z : U) (w w' : TangentSpace (𝓡 3) z),
        (G.metric 0).inner z w w' = d.pullbackInner 0 h0 z.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w')) →
      (∀ z : U, (G.connection 0).curvatureTensorNorm z =
        (H.generalized.connection (base + 0 / Q)).curvatureTensorNorm
          (d.forward 0 h0 z.val) / Q) →
      (∀ z : U, (G.connection 0).curvatureTensorNorm z ≤ K) →
      let j : PartialDiffeomorph (𝓡 3) (𝓡 3) U (F.slice base).carrier ∞ :=
        terminalSourceNormal_terminalMap U p0
        (terminalSourceNormal_historyCylinder H U htime d) h0
      (∀ z : U, j z = z.val) →
      RegularNormalStageOutput (G.metric 0) p0 (F.metric base) Q j a Rchart rho Hbar R := by
  let L := max 1 (9 * K)
  let Hbar := 13 * max (4 * L / 3) 1
  have hH : 0 ≤ Hbar := mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 1).trans
    (le_max_right _ _))
  have hKH : K ≤ Hbar := by
    have hKL : 9 * K ≤ L := le_max_right _ _
    have hmax : 4 * L / 3 ≤ max (4 * L / 3) 1 := le_max_left _ _
    dsimp only [Hbar]
    nlinarith only [hK, hKL, hmax]
  obtain ⟨rho, hrho, hrhoR, hsmall, factory⟩ :=
    terminalSource_exists_physical_stage hH ha hr hv haR har
  refine ⟨rho, hrho, hrhoR, hsmall, ?_⟩
  intro F W H base tau0 tau hbase htau0 htau x
  let Q := H.generalized.scalar ⟨base, x⟩
  let U : TopologicalSpace.Opens (F.slice base).carrier :=
    ⟨(F.metric base).ball (H.history.forward base hbase x) (A / Real.sqrt Q),
      M04.initial_ball_isOpen _ _ _⟩
  dsimp only
  intro e hbased hvolume p0 hp0 htime d G hmetric hnorm hbound hmap
  let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
  let ereal := terminalSourceNormal_historyCylinder H U htime d
  let j := terminalSourceNormal_terminalMap U p0 ereal h0
  have hjmap (z : U) : j z = z.val := hmap z
  have hconvert := terminalSourceNormal_historyCylinder_maps H U htime d
  have hm (z : U) (w w' : TangentSpace (𝓡 3) z) :
      (G.metric 0).inner z w w' = ereal.pullbackInner 0 h0 z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice base).carrier) z w') :=
    (hmetric z w w').trans (hconvert.2 0 h0 z.val z.property _ _).symm
  have hn (z : U) : (G.connection 0).curvatureTensorNorm z =
      (F.connection (base + 0 / Q)).curvatureTensorNorm (ereal.forward 0 h0 z.val) / Q := by
    rw [congrFun (hconvert.1 0 h0) z, H.curvature_norm_pullback]
    exact hnorm z
  have hread := terminalSourceNormal_terminal_readouts U p0 ereal h0 G hm hn
  have hj := terminalSourceNormal_terminal_map U p0 ereal h0
  have htarget : j.target = U := by
    rw [hj.2.1]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change j z ∈ U
      rw [hjmap z]
      exact z.property
    · intro hy
      exact ⟨⟨y, hy⟩, hmap ⟨y, hy⟩⟩
  have hcenter : j p0 = H.history.forward base hbase x := (hmap p0).trans hp0
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr e.scale_pos
  have hcover : (F.metric base).ball (j p0) (6 * R / Real.sqrt Q) ⊆ j.target := by
    rw [hcenter, htarget]
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hlarge hroot.le))
  have hcurv : ∀ z ∈ (F.metric base).ball (j p0) (5 * R / Real.sqrt Q),
      (F.connection base).curvatureTensorNorm z ≤ Hbar * Q := by
    intro z hz
    have hR : 0 < R := ha.trans_le haR
    have hzU : z ∈ U := by
      change z ∈ (U : Set (F.slice base).carrier)
      rw [← htarget]
      exact hcover (hz.trans_le (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith) hroot.le)))
    have h := (hbound ⟨z, hzU⟩).trans hKH
    rw [hread.2, hmap] at h
    exact (div_le_iff₀ e.scale_pos).mp h
  have hrA : r / Real.sqrt Q < A / Real.sqrt Q :=
    div_lt_div_of_pos_right (by linarith [ha.trans_le haR]) hroot
  have hvolEq := (terminalSource_regular_history_ball_buffer H hbase htau0 x
    (div_pos hr hroot).le hrA e hbased).2.2
  have hvol : ENNReal.ofReal (v / Real.sqrt Q ^ 3) ≤ calibratedMetricVolume (F.metric base)
      ((F.metric base).ball (j p0) (r / Real.sqrt Q)) := by
    rw [hcenter, ← hvolEq]
    exact hvolume
  obtain ⟨cover, hquadratic⟩ := factory F (F.slice base) base Q tau U p0 ereal h0 G
    hm hn (hj.2.1 ▸ hcover) hcurv hvol
  exact ⟨cover, hquadratic, hread.1, hcover⟩

end PoincareConjecture.M47
