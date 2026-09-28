import PoincareConjecture.Proofs.M10.MinimumInitialLimit
import PoincareConjecture.Proofs.M10.HessianMinimum
import PoincareConjecture.Proofs.M10.BarrierLipschitz











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem sInf_reducedLength_mul_sub_le
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hcont : ContinuousOn (fun s : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q s)))
      (Ioo 0 τmax))
    (hattain : ∀ s ∈ Ioo 0 τmax, ∃ q : M,
      reducedLength F T p q s = sInf (range (fun y ↦ reducedLength F T p y s)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < τmax) :
    b * sInf (range (fun q ↦ reducedLength F T p q b)) -
        a * sInf (range (fun q ↦ reducedLength F T p q a)) ≤
      (n : ℝ) / 2 * (b - a) := by
  let m := fun s : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q s))
  have hcomparison : ∀ x ∈ Icc a b, x * m x ≤ a * m a + (n : ℝ) / 2 * (x - a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary
      (continuousOn_id.mul (hcont.mono (fun s hs ↦ ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩)))
      (B' := fun _ ↦ (n : ℝ) / 2)
    · simp [m]
    · fun_prop
    · intro x _
      simpa only [mul_one, id_eq] using
        ((((hasDerivAt_id x).sub_const a).const_mul ((n : ℝ) / 2)).const_add
          (a * m a)).hasDerivWithinAt
    · intro x hx r hr
      have hxI : x ∈ Ioo 0 τmax := ⟨ha.trans_le hx.1, hx.2.trans hb⟩
      let ε : ℝ := (r - (n : ℝ) / 2) / (2 * x)
      have hε : 0 < ε := div_pos (sub_pos.mpr hr) (mul_pos (by norm_num) hxI.1)
      obtain ⟨q, hq⟩ := hattain x hxI
      obtain ⟨B, hres⟩ := hDifferential.upper_barrier_extension p q x hxI.1 hxI.2 ε hε
      have hmin : IsLocalMin (fun y ↦ B.representative (y, x)) q := by
        have hnear := (continuous_id.prodMk continuous_const).continuousAt
          (B.neighborhood_open.mem_nhds B.center_mem)
        change ∀ᶠ y in 𝓝 q, B.representative (q, x) ≤ B.representative (y, x)
        filter_upwards [hnear] with y hy
        rw [B.touches, hq]
        exact (csInf_le (reducedLength_range_bddBelow hL G hcurvature hxI.1 hxI.2)
          (mem_range_self y)).trans (B.dominates (y, x) hy)
      have hlap := laplacian_nonneg_of_isLocalMin (F.metric (T - x)) (F.connection (T - x))
        (B.representative_space_smooth.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) hmin
      obtain ⟨d, hd⟩ := B.representative_time_derivative
      have hS : HasDerivAt (fun s : ℝ ↦ s * B.representative (q, s))
          (B.representative (q, x) + x * d) x := by
        simpa only [Pi.mul_def, id_eq, one_mul] using! (hasDerivAt_id x).mul hd
      have heq : x * B.representative (q, x) = x * m x := by rw [B.touches, hq]
      have hupper : ∀ᶠ s in 𝓝 x, s * m s ≤ s * B.representative (q, s) := by
        have hnear := (continuous_const.prodMk continuous_id).continuousAt
          (B.neighborhood_open.mem_nhds B.center_mem)
        filter_upwards [hnear, isOpen_Ioo.mem_nhds hxI] with s hs hstime
        apply mul_le_mul_of_nonneg_left _ hstime.1.le
        exact (csInf_le (reducedLength_range_bddBelow hL G hcurvature hstime.1 hstime.2)
          (mem_range_self q)).trans (B.dominates (q, s) hs)
      have hderiv : B.representative (q, x) + x * d < r := by
        change deriv (fun s ↦ B.representative (q, s)) x +
          (F.connection (T - x)).laplacian (fun y ↦ B.representative (y, x)) q -
            ((n : ℝ) / 2 - B.representative (q, x)) / x ≤ ε at hres
        rw [hd.deriv] at hres
        have hmul := mul_le_mul_of_nonneg_left hres hxI.1.le
        have hcancel : x * (((n : ℝ) / 2 - B.representative (q, x)) / x) =
            (n : ℝ) / 2 - B.representative (q, x) := by field_simp [hxI.1.ne']
        rw [mul_sub, mul_add, hcancel] at hmul
        have hεx : x * ε = (r - (n : ℝ) / 2) / 2 := by
          dsimp only [ε]
          field_simp [hxI.1.ne']
        rw [hεx] at hmul
        nlinarith only [hmul, mul_nonneg hxI.1.le hlap, hr]
      exact frequently_slope_lt_of_upper_support hS heq hupper hderiv
  exact sub_le_iff_le_add.mpr
    (by simpa only [add_comm] using hcomparison b ⟨hab, le_rfl⟩)


theorem reducedLength_minimum_bound_of_attainment
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hcont : ContinuousOn (fun s : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q s)))
      (Ioo 0 τmax))
    (hattain : ∀ s ∈ Ioo 0 τmax, ∃ q : M,
      reducedLength F T p q s = sInf (range (fun y ↦ reducedLength F T p y s)))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax) :
    ∃ q : M, (∀ y : M, reducedLength F T p q b ≤ reducedLength F T p y b) ∧
      reducedLength F T p q b ≤ (n : ℝ) / 2 := by
  let m := fun s : ℝ ↦ sInf (range (fun q ↦ reducedLength F T p q s))
  have hzero := sInf_reducedLength_tendsto_zero hL G hmax hT hwindow hcurvature
  have hid : Tendsto (id : ℝ → ℝ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun a : ℝ ↦ a * m a + (n : ℝ) / 2 * (b - a))
      (𝓝[>] (0 : ℝ)) (𝓝 ((n : ℝ) / 2 * b)) := by
    simpa only [zero_mul, sub_zero, zero_add, id_eq, m] using
      (hid.mul hzero).add ((tendsto_const_nhds.sub hid).const_mul ((n : ℝ) / 2))
  have hbound : b * m b ≤ (n : ℝ) / 2 * b := by
    apply ge_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hb] with a ha
    have h := sInf_reducedLength_mul_sub_le hL G hDifferential hcurvature hcont hattain
      ha.1 ha.2.le hbmax
    dsimp only [m]
    linarith only [h]
  obtain ⟨q, hq⟩ := hattain b ⟨hb, hbmax⟩
  refine ⟨q, ?_, ?_⟩
  · intro y
    rw [hq]
    exact csInf_le (reducedLength_range_bddBelow hL G hcurvature hb hbmax) (mem_range_self y)
  · rw [hq]
    change m b ≤ (n : ℝ) / 2
    nlinarith only [hbound, hb]

end PoincareConjecture.M10
