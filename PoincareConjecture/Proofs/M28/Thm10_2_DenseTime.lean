import PoincareConjecture.Proofs.M28.Generalized.GoodSlicePath
import PoincareConjecture.Proofs.M28.Generalized.ShortPaths
import PoincareConjecture.Proofs.M28.Generalized.CanonicalAdapters
import PoincareConjecture.Statements.M28BoundedDistance

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem dense_rebase_radius (A q : ℝ) (hq : 0 < q) :
    ((A + 1) * Real.sqrt 2) * (2 * q) ^ (-1 / 2 : ℝ) =
      (A + 1) * q ^ (-1 / 2 : ℝ) := by
  rw [Real.rpow_div_two_eq_sqrt _ (by positivity),
    Real.rpow_div_two_eq_sqrt _ hq.le, Real.rpow_neg_one, Real.rpow_neg_one,
    Real.sqrt_mul (by norm_num)]
  have htwo : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

theorem dense_time_of_same_time
    (P : RicciFlowCurvatureTheory.{u}) {epsilon₀ : ℝ}
    (hsame : M28SameTimeEstimateStatement.{u} epsilon₀) :
    M28DenseTimeEstimateStatement.{u} epsilon₀ := by
  intro epsilon hepsilon hle C hC A hA
  obtain ⟨D₀, D, hD₀, hD, bound⟩ :=
    hsame epsilon hepsilon hle C hC ((A + 1) * Real.sqrt 2) (by positivity)
  refine ⟨D₀ / 2, max 4 (2 * D), by positivity,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro F hpinched t ht x hx hdense y hy
  by_contra hnot
  let q := F.scalar ⟨t, x⟩
  have hq : 0 < q := lt_of_lt_of_le (div_pos hD₀ (by norm_num)) hx
  have hbad : max 4 (2 * D) * q < F.scalar ⟨t, y⟩ := lt_of_not_ge hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hγlength, _, _⟩ :=
    (F.metric t).exists_short_path_of_mem_ball hy
  have hpow : 0 < q ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
  have hmargin : A * q ^ (-1 / 2 : ℝ) < (A + 1) * q ^ (-1 / 2 : ℝ) := by
    nlinarith
  have hlength : (F.metric t).pathELength γ 0 1 <
      ENNReal.ofReal ((A + 1) * q ^ (-1 / 2 : ℝ)) :=
    hγlength.trans ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hmargin)
  obtain ⟨s, hs, η, hη, hstart, hend, hηlength, hgood⟩ :=
    exists_good_slice_path F P ht x hdense γ hγ
      (Rstart := 2 * q) (Rend := max 4 (2 * D) * q)
      (by rw [hγ0]; change q < 2 * q; linarith)
      (by simpa only [hγ1] using hbad) hlength
  have hscalar : ContinuousOn (fun v => F.scalar ⟨s, η v⟩) (Icc 0 1) :=
    (F.continuous_scalar_slice P s).comp_continuousOn hη.continuousOn
  have hhigh : 2 * q < F.scalar ⟨s, η 1⟩ := by
    have hm := mul_le_mul_of_nonneg_right (le_max_left (4 : ℝ) (2 * D)) hq.le
    nlinarith
  obtain ⟨v, hv, heq, _⟩ :=
    exists_last_eq_of_continuousOn zero_le_one hscalar hstart.le hhigh
  have hthreshold : D₀ ≤ F.scalar ⟨s, η v⟩ := by
    rw [heq]
    change D₀ / 2 ≤ q at hx
    linarith
  have hcanonical : generalizedSliceStrongCanonicalNeighborhoods F epsilon C
      (4 * F.scalar ⟨s, η v⟩) s := by
    rw [heq]
    apply hgood.mono_cutoff
    change 4 * q ≤ 4 * (2 * q)
    linarith
  have hball : η 1 ∈ (F.metric s).ball (η v)
      (((A + 1) * Real.sqrt 2) * F.scalar ⟨s, η v⟩ ^ (-1 / 2 : ℝ)) := by
    change (F.metric s).edist (η v) (η 1) < _
    rw [heq, dense_rebase_radius A q hq]
    apply lt_of_le_of_lt _ hηlength
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice s).carrier → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    exact (Manifold.riemannianEDist_le_pathELength
      (hη.mono (Icc_subset_Icc hv.1 le_rfl)) rfl rfl hv.2).trans
        (Manifold.pathELength_mono hv.1 le_rfl)
  have hbound := bound F hpinched s hs (η v) hthreshold hcanonical (η 1) hball
  rw [heq] at hbound
  have hm := mul_le_mul_of_nonneg_right (le_max_right (4 : ℝ) (2 * D)) hq.le
  nlinarith

end PoincareConjecture.M28
