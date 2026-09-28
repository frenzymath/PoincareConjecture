import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeChartBound
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ChartReaderProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ChartReadable_local_correction
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M) :
    ∃ (U : Set M) (r B : ℝ) (T : E → M), IsOpen U ∧ p ∈ U ∧ 0 < r ∧ 0 ≤ B ∧
      (∀ q ∈ U, T (e q) = q ∧ dist (e q) (e p) < r / 2) ∧
      (∀ y ∈ closedBall (e p) r, ContMDiffAt (𝓡 m) (𝓡 n) 1 T y) ∧
      ∀ y ∈ closedBall (e p) r, ∀ v : E,
        g.tangentNorm (T y) (mfderiv (𝓡 m) (𝓡 n) T y v) ≤ B * ‖v‖ := by
  obtain ⟨b, hb, L, hL⟩ := hread p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  have hp : p ∈ c.source := by simpa only [extChartAt_source] using hb
  have hreader : (L ∘ e) =ᶠ[𝓝 p] c := by
    change (fun q => L (e q)) =ᶠ[𝓝 p] c
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hL
  have hLp : L (e p) = c p := hreader.self_of_nhds
  have hpre : L ⁻¹' c.target ∈ 𝓝 (e p) :=
    (c.open_target.preimage L.continuous).mem_nhds (by
      rw [mem_preimage, hLp]
      exact c.map_source hp)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let r := a / 2
  have hr : 0 < r := half_pos ha
  have hclosed : closedBall (e p) r ⊆ L ⁻¹' c.target := by
    intro y hy
    apply hball
    exact (mem_closedBall.mp hy).trans_lt (by dsimp only [r]; linarith)
  let T : E → M := c.symm ∘ L
  have hT (y : E) (hy : y ∈ closedBall (e p) r) :
      ContMDiffAt (𝓡 m) (𝓡 n) 1 T y := by
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) 1 c.symm (L y) :=
      (contMDiffOn_chart_symm : ContMDiffOn (𝓡 n) (𝓡 n) 1 c.symm c.target).contMDiffAt
        (c.open_target.mem_nhds (hclosed hy))
    exact hc.comp y L.contDiff.contMDiff.contMDiffAt
  obtain ⟨B, hB, hbound⟩ := m64_euclidean_target_differential_bound_on_compact g
    (isCompact_closedBall (e p) r) T hT
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp
    (inter_mem (c.open_source.mem_nhds hp) hreader)
  let U := V ∩ e ⁻¹' ball (e p) (r / 2)
  refine ⟨U, r, B, T, hVopen.inter (isOpen_ball.preimage he.continuous),
    ⟨hpV, mem_ball_self (half_pos hr)⟩, hr, hB, ?_, hT, hbound⟩
  intro q hq
  refine ⟨?_, hq.2⟩
  change c.symm (L (e q)) = q
  have hh : L (e q) = c q := (hVsub hq.1).2
  rw [hh, c.left_inv (hVsub hq.1).1]

theorem m64ChartReadable_local_correction_into
    (g : RiemannianMetric n M) (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hread : M60.SUChartReadable (n := n) e) (p : M)
    (O : Set M) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (U : Set M) (r B : ℝ) (T : E → M), IsOpen U ∧ p ∈ U ∧ 0 < r ∧ 0 ≤ B ∧
      (∀ q ∈ U, T (e q) = q ∧ dist (e q) (e p) < r / 2) ∧
      MapsTo T (closedBall (e p) r) O ∧
      (∀ y ∈ closedBall (e p) r, ContMDiffAt (𝓡 m) (𝓡 n) 1 T y) ∧
      ∀ y ∈ closedBall (e p) r, ∀ v : E,
        g.tangentNorm (T y) (mfderiv (𝓡 m) (𝓡 n) T y v) ≤ B * ‖v‖ := by
  obtain ⟨U, r, B, T, hU, hp, hr, hB, hfix, hT, hbound⟩ :=
    m64ChartReadable_local_correction g e he hread p
  have hTp : T (e p) = p := (hfix p hp).1
  have hpre : T ⁻¹' O ∈ 𝓝 (e p) :=
    ((hT _ (mem_closedBall_self hr.le)).continuousAt).preimage_mem_nhds
      (hO.mem_nhds (hTp.symm ▸ hpO))
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let r' := min r (a / 2)
  have hr' : 0 < r' := lt_min hr (half_pos ha)
  have hsub : closedBall (e p) r' ⊆ closedBall (e p) r :=
    closedBall_subset_closedBall (min_le_left _ _)
  have hmap : MapsTo T (closedBall (e p) r') O := by
    intro y hy
    exact hball ((mem_closedBall.mp hy).trans_lt
      ((min_le_right r (a / 2)).trans_lt (by linarith)))
  let V := U ∩ e ⁻¹' ball (e p) (r' / 2)
  refine ⟨V, r', B, T, hU.inter (isOpen_ball.preimage he.continuous),
    ⟨hp, mem_ball_self (half_pos hr')⟩, hr', hB,
    fun q hq => ⟨(hfix q hq.1).1, hq.2⟩, hmap,
    fun y hy => hT y (hsub hy), fun y hy => hbound y (hsub hy)⟩

end PoincareConjecture
