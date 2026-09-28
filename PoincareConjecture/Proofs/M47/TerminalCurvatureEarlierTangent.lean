import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactBuffers
import PoincareConjecture.Proofs.M47.TerminalCurvatureCompactCoefficients
import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialChartMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private theorem quadratic_of_coefficient_error
    {B B0 : Bilin} {b : ℝ} (herror : ‖B - B0‖ ≤ b / 2)
    (hlow : ∀ w : E, b * ‖w‖ ^ 2 ≤ B0 w w) (w : E) :
    B0 w w ≤ 2 * B w w := by
  have herr : |B w w - B0 w w| ≤ (b / 2) * ‖w‖ ^ 2 := by
    calc
      _ = ‖(B - B0) w w‖ := by simp only [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖(B - B0) w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖B - B0‖ * ‖w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ((b / 2) * ‖w‖) * ‖w‖ := by gcongr
      _ = _ := by ring
  nlinarith [hlow w, neg_le_of_abs_le herr]

private theorem quadratic_of_original_chart
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X M ∞)
    (c : PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    {x : X} (hx : x ∈ c.source) (hxphi : x ∈ phi.source)
    (hcoeff : ∀ w : E, h.pullbackCoefficients c.symm (c x) w w ≤
      2 * g.pullbackCoefficients (phi ∘ c.symm) (c x) w w)
    (v : TangentSpace (𝓡 3) x) :
    h.inner x v v ≤ 2 * g.inner (phi x)
      (mfderiv (𝓡 3) (𝓡 3) phi x v) (mfderiv (𝓡 3) (𝓡 3) phi x v) := by
  have hlocal := c.symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (c.map_source hx)
  have hsurj : Function.Surjective (mfderiv (𝓡 3) (𝓡 3) c.symm (c x)) :=
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  obtain ⟨w, hw⟩ := hsurj v
  have hphi := (phi.contMDiffOn_toFun.contMDiffAt
    (phi.open_source.mem_nhds hxphi)).mdifferentiableAt (by simp)
  have hleft : c.symm (c x) = x := c.left_inv hx
  have hphi' : MDifferentiableAt (𝓡 3) (𝓡 3) phi (c.symm (c x)) := by
    rwa [hleft]
  have hd := mfderiv_comp (c x) hphi' (hlocal.mdifferentiableAt (by simp))
  have hpair := hcoeff w
  change h.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) ≤
    2 * g.inner (phi (c.symm (c x)))
      (mfderiv (𝓡 3) (𝓡 3) (phi ∘ c.symm) (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) (phi ∘ c.symm) (c x) w) at hpair
  rw [hd] at hpair
  change h.inner (c.symm (c x))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w) ≤
    2 * g.inner (phi (c.symm (c x)))
      (mfderiv (𝓡 3) (𝓡 3) phi (c.symm (c x))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w))
      (mfderiv (𝓡 3) (𝓡 3) phi (c.symm (c x))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c x) w)) at hpair
  rw [hw, hleft] at hpair
  exact hpair

theorem terminalCurvature_eventually_compact_tangent
    {ι : Type*}
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X]
    (g : ∀ k, RiemannianMetric 3 (M k)) (h : RiemannianMetric 3 X)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hcoverC : ∀ x : X, ∃ i, x ∈ (c i).source)
    (hjet : ∀ i K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 ((g k).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ 0 (h.pullbackCoefficients (c i).symm)) atTop K)
    (V : Set X) (hV : IsCompact V) :
    ∀ᶠ k in atTop, V ⊆ U k ∧ ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm x v ≤ 2 * (g k).tangentNorm (phi k x)
        (mfderiv (𝓡 3) (𝓡 3) (phi k) x v) := by
  classical
  by_cases hne : V.Nonempty
  · obtain ⟨s, _hsne, index, K, hK, hKtarget, hcoverK⟩ :=
      terminalCurvature_exists_finite_original_chart_buffers c hV hne
        (fun x _ => hcoverC x)
    let B0 (j : s) := h.pullbackCoefficients (c (index j)).symm
    let B (j : s) (k : ℕ) := (g k).pullbackCoefficients (phi k ∘ (c (index j)).symm)
    have hpos (j : s) (y : E) (hy : y ∈ K j) (w : E) (hw : w ≠ 0) :
        0 < B0 j y w w := by
      have hlocal := (c (index j)).symm.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (hKtarget j hy)
      have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (c (index j)).symm y) :=
        (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
      apply h.pos
      intro hz
      apply hw
      apply hinj
      rw [map_zero]
      convert! hz using 1
    choose b hb hlow using fun j : s => exists_uniform_bilinear_lower_bound (hK j)
      ((terminalCurvature_partial_chart_coefficients h (c (index j))).1.continuousOn.mono
        (hKtarget j)) (hpos j)
    have hfinite : ∀ᶠ k in atTop, ∀ j : s, ∀ y ∈ K j, ∀ w : E,
        B0 j y w w ≤ 2 * B j k y w w := by
      apply Filter.eventually_all.mpr
      intro j
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp
        (hjet (index j) (K j) (hK j) (hKtarget j)) (b j / 2) (half_pos (hb j))]
        with k hk y hy w
      have hdiff := (hk y hy).le
      rw [dist_comm, dist_eq_norm] at hdiff
      have herror : ‖B j k y - B0 j y‖ ≤ b j / 2 := by
        have heq : iteratedFDeriv ℝ 0 (B j k) y - iteratedFDeriv ℝ 0 (B0 j) y =
            iteratedFDeriv ℝ 0 (fun z => B j k z - B0 j z) y := by
          ext v
          rfl
        change ‖iteratedFDeriv ℝ 0 (B j k) y - iteratedFDeriv ℝ 0 (B0 j) y‖ ≤ _ at hdiff
        rw [heq, norm_iteratedFDeriv_zero] at hdiff
        exact hdiff
      exact quadratic_of_coefficient_error herror (hlow j y hy) w
    obtain ⟨j0, hj0⟩ := hV.elim_directed_cover U hU
      (by rw [hcover]; exact subset_univ _) hmono.directed_le
    filter_upwards [hfinite, eventually_ge_atTop j0] with k hk hj0k
    have hVU : V ⊆ U k := hj0.trans (hmono hj0k)
    refine ⟨hVU, ?_⟩
    intro x hx v
    obtain ⟨j, hxj, hxK⟩ := hcoverK x hx
    have hxphi : x ∈ (phi k).source := by rw [hsource k]; exact hVU hx
    have hquad := quadratic_of_original_chart (g k) h (phi k) (c (index j))
      hxj hxphi (hk j (c (index j) x) hxK) v
    have hn : 0 ≤ (g k).inner (phi k x)
        (mfderiv (𝓡 3) (𝓡 3) (phi k) x v) (mfderiv (𝓡 3) (𝓡 3) (phi k) x v) := by
      by_cases hv : mfderiv (𝓡 3) (𝓡 3) (phi k) x v = 0
      · simp [hv]
      · exact ((g k).pos _ _ hv).le
    change Real.sqrt (h.inner x v v) ≤ 2 * Real.sqrt _
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hn]
    norm_num
    linarith
  · have hVempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst V
    exact Filter.Eventually.of_forall (fun _ => by simp)

end PoincareConjecture.M47
