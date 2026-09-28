import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.HalfDiskCollarRectangle






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Gauss M65StrictTrace






theorem finite_halfDisk_frame_collar_limit {ι : Type*} [Finite ι] {n : ℕ}
    (g : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : ∀ i, LeviCivitaData (g i))
    (H : ι → ℂ → EuclideanSpace ℝ (Fin n))
    (F : ι → ℂ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (w : ι → ℂ → ℝ) (R e C a b : ι → ℝ)
    (he : ∀ i, 0 < e i) (heR : ∀ i, 2 * e i < R i) (hC : ∀ i, 0 ≤ C i)
    (hab : ∀ i, a i ≤ b i) (hcell : ∀ i, Icc (a i) (b i) ⊆ Icc (-(e i)) (e i))
    (hH : ∀ i, ContDiffOn ℝ 1 (H i) (closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im}))
    (hw : ∀ i, ContDiffOn ℝ 1 (w i) (closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im}))
    (hF : ∀ i, ContinuousOn (F i) (closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im}))
    (hF1 : ∀ i, ContDiffOn ℝ 1 (F i) (ball (0 : ℂ) (R i) ∩ {z | 0 < z.im}))
    (hDF : ∀ i, MemLp (fun z => fderiv ℝ (F i) z 1)
      2 (volume.restrict (ball (0 : ℂ) (R i) ∩ {z | 0 < z.im})))
    (hT0 : ∀ i, ∀ t ∈ Icc (-(e i)) (e i),
      ContDiffAt ℝ 1 (fun s : ℝ => (F i (s : ℂ)).1) t)
    (hholder : ∀ i, ∀ z ∈ closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im},
      ∀ y ∈ closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im},
        ‖F i z - F i y‖ ≤ C i * Real.sqrt ‖z - y‖) :
    ∃ delta : ℝ, 0 < delta ∧ (∀ i, delta < e i) ∧
      ∃ h : ℕ → ℝ, (∀ k, h k ∈ Ioo (0 : ℝ) delta) ∧ Tendsto h atTop (𝓝 0) ∧
        ∀ i, Tendsto (fun k => ∫ t in (a i)..(b i),
          let z := (t : ℂ) + (h k : ℂ) * I
          w i z * (g i).inner (H i z)
            (covariantDerivativeAlongMap (D i) (H i) (fun z => (F i z).1) z 1) (F i z).2) atTop
          (𝓝 (∫ t in (a i)..(b i), w i (t : ℂ) * (g i).inner (H i (t : ℂ))
            (deriv (fun s : ℝ => (F i (s : ℂ)).1) t +
              connectionCoefficient (D i) (H i (t : ℂ))
                (fderivWithin ℝ (H i) (closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im})
                  (t : ℂ) 1) (F i (t : ℂ)).1) (F i (t : ℂ)).2)) := by
  have hnear : ∀ᶠ d : ℝ in 𝓝 0, ∀ i, d < e i :=
    eventually_all.mpr (fun i => gt_mem_nhds (he i))
  obtain ⟨rho, hrho, hsub⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  let delta := rho / 2
  have hd : 0 < delta := half_pos hrho
  have hde : ∀ i, delta < e i := hsub (mem_closedBall_zero_iff.mpr (by
    rw [Real.norm_eq_abs, abs_of_pos hd]
    dsimp only [delta]
    linarith))
  let K := fun i => closedBall (0 : ℂ) (R i) ∩ {z | 0 ≤ z.im}
  let W := fun i => ball (0 : ℂ) (R i) ∩ {z | 0 < z.im}
  have hR (i : ι) : 0 < R i := (by linarith [he i] : 0 < 2 * e i).trans (heR i)
  have hWK (i : ι) : W i ⊆ K i := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  have hrect (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (h : ℝ) (hh : h ∈ Icc (0 : ℝ) delta) : (t : ℂ) + (h : ℂ) * I ∈ K i := by
    refine ⟨mem_closedBall_zero_iff.mpr (collar_rectangle_norm_lt (heR i) (hcell i ht)
      ⟨hh.1, hh.2.trans (hde i).le⟩).le, ?_⟩
    simpa using hh.1
  have hrectU (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i))
      (h : ℝ) (hh : h ∈ Ioo (0 : ℝ) delta) : (t : ℂ) + (h : ℂ) * I ∈ W i := by
    refine ⟨mem_ball_zero_iff.mpr (collar_rectangle_norm_lt (heR i) (hcell i ht)
      ⟨hh.1.le, hh.2.le.trans (hde i).le⟩), ?_⟩
    simpa using hh.1
  have hDN (i : ι) : MemLp (fun z => fderiv ℝ (fun y => (F i y).2) z 1)
      2 (volume.restrict (K i ∩ W i)) := by
    rw [inter_eq_right.mpr (hWK i)]
    have hp := (hDF i).continuousLinearMap_comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    apply hp.ae_eq
    filter_upwards [ae_restrict_mem ((halfDisk_differential_domain (hR i)).1.measurableSet)]
      with z hz
    have hzD := ((hF1 i).contDiffAt
      ((halfDisk_differential_domain (hR i)).1.mem_nhds hz)).differentiableAt one_ne_zero
    simpa using congrArg (fun L => L (1 : ℂ)) hzD.hasFDerivAt.snd.fderiv.symm
  refine ⟨delta, hd, hde, ?_⟩
  apply finite_weighted_connection_collar_limit g D H
    (fun i z => (F i z).1) (fun i z => (F i z).2) w
    (fun i => (isCompact_closedBall (0 : ℂ) (R i)).inter_right
      (isClosed_le continuous_const continuous_im))
    (fun i => (halfDisk_differential_domain (hR i)).2.2.1)
    (fun i => (halfDisk_differential_domain (hR i)).1) hWK hH hw
    (fun i => (hF i).fst) (fun i => (hF1 i).fst)
    (fun i => (hF i).snd) (fun i => (hF1 i).snd) hDN
    a b C hd hab hC hrect hrectU (fun i t ht => hT0 i t (hcell i ht))
  intro i z hz y hy
  exact (norm_fst_le (F i z - F i y)).trans (hholder i z hz y hy)

end PoincareConjecture.M64
