import PoincareConjecture.Proofs.M25.Topology3D.Plane.ShiftedRoundedSampling
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineChords
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

private theorem rounded_affine_grid_axis_of_nearby
    (c : ℝ → ℝ × ℝ) (ρ : ℝ → ℝ) {a0 h u : ℝ}
    (hh : 0 < h) (hhalf : h < 1 / 2)
    (hc : ∀ v, |v - u| < 1 → c v = (v, 0)) :
    roundedVertexPath ρ (fun i : ℤ => c (a0 + h * i)) ((u - a0) / h) = (u, 0) := by
  let j : ℤ := ⌊(u - a0) / h + 1 / 2⌋
  let B : ℝ := a0 + h * j
  have hjlo : (j : ℝ) ≤ (u - a0) / h + 1 / 2 := Int.floor_le _
  have hjhi : (u - a0) / h + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hBlo : u - h / 2 < B := by
    have hd := (div_lt_iff₀ hh).mp
      (show (u - a0) / h < (j : ℝ) + 1 / 2 by linarith)
    dsimp [B]
    nlinarith
  have hBhi : B ≤ u + h / 2 := by
    have hd := (le_div_iff₀ hh).mp
      (show (j : ℝ) - 1 / 2 ≤ (u - a0) / h by linarith)
    dsimp [B]
    nlinarith
  have hnear (v : ℝ) (hv : v ∈ Icc (B - h) (B + h)) : |v - u| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hv.1, hv.2]
  have hprev : a0 + h * ((j - 1 : ℤ) : ℝ) = B - h := by
    simp only [Int.cast_sub, Int.cast_one]
    dsimp [B]
    ring
  have hnext : a0 + h * ((j + 1 : ℤ) : ℝ) = B + h := by
    simp only [Int.cast_add, Int.cast_one]
    dsimp [B]
    ring
  have hc0 := hc B (hnear B ⟨by linarith, by linarith⟩)
  have hcm := hc (B - h) (hnear (B - h) ⟨le_rfl, by linarith⟩)
  have hcp := hc (B + h) (hnear (B + h) ⟨by linarith, le_rfl⟩)
  change roundedCorner ρ (c B) (c B - c (a0 + h * ((j - 1 : ℤ) : ℝ)))
    (c (a0 + h * ((j + 1 : ℤ) : ℝ)) - c B) ((u - a0) / h - j) = (u, 0)
  rw [hprev, hnext, hc0, hcm, hcp]
  ext <;> dsimp [roundedCorner, B] <;> field_simp <;> ring

theorem exists_uniform_rounded_openLine_tube_certificate
    (C : (ℝ × ℝ) × ℝ → ℝ × ℝ) (hC : ContDiff ℝ ∞ C)
    {R : ℝ} (_hR : 0 < R)
    (hTail : ∀ z u, R ≤ |u| → C (z, u) = (u, 0))
    (T : OpenPartialHomeomorph
      ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hTarget : ∀ z ∈ K, ∀ u, (z, C (z, u)) ∈ T.target)
    (hRecover : ∀ z ∈ K, ∀ u, T.symm (z, C (z, u)) = (z, (u, 0)))
    {A : ℝ} (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ a0 h : ℝ, 0 < h → h < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ →
          (∀ s, δ ≤ |s| → ρ s = |s|) →
          (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
          (∀ s, |deriv ρ s| ≤ 1) →
          let G : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p =>
            roundedVertexPath ρ (fun i : ℤ => C (p.1, a0 + h * i))
              ((p.2 - a0) / h)
          ContDiff ℝ ∞ G ∧
            (∀ z u, R + 2 ≤ |u| → G (z, u) = (u, 0)) ∧
            (∀ z, (∀ u, C (z, u) = (u, 0)) → ∀ u, G (z, u) = (u, 0)) ∧
            ∀ z ∈ K, ∀ u,
              (z, G (z, u)) ∈ T.target ∧
                0 < fderiv ℝ
                  (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (T.symm p).2.1)
                  (z, G (z, u)) (0, deriv (fun v => G (z, v)) u) ∧
                |(T.symm (z, G (z, u))).2.2| < A := by
  let D : (ℝ × ℝ) × ℝ → ℝ × ℝ :=
    fun p => fderiv ℝ (fun v => C (p.1, v)) p.2 1
  have hD : ContDiff ℝ ∞ D := by
    have hunc : ContDiff ℝ ∞
        (Function.uncurry (fun p : (ℝ × ℝ) × ℝ => fun u => C (p.1, u))) :=
      hC.comp (contDiff_fst.fst.prodMk contDiff_snd)
    exact hunc.fderiv_apply (n := ∞) contDiff_snd contDiff_const (by simp)
  have hd (z : ℝ × ℝ) (u : ℝ) : HasDerivAt (fun v => C (z, v)) (D (z, u)) u :=
    ((hC.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp) u).hasFDerivAt.hasDerivAt
  let P : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => (T.symm p).2.1
  let H : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => (T.symm p).2.2
  have hP : ContDiffOn ℝ ∞ P T.target := hInv.snd.fst
  have hH : ContDiffOn ℝ ∞ H T.target := hInv.snd.snd
  have hcal (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) :
      fderiv ℝ P (z, C (z, u)) (0, D (z, u)) = 1 := by
    have hp : HasFDerivAt P (fderiv ℝ P (z, C (z, u))) (z, C (z, u)) :=
      (hP.contDiffAt (T.open_target.mem_nhds (hTarget z hz u))).differentiableAt
        (by simp) |>.hasFDerivAt
    have hconst : HasFDerivAt (fun _ : ℝ => z)
        (0 : ℝ →L[ℝ] (ℝ × ℝ)) u := hasFDerivAt_const z u
    have hcomp : HasDerivAt (fun v => P (z, C (z, v)))
        (fderiv ℝ P (z, C (z, u)) (0, D (z, u))) u := by
      simpa [Function.comp_def] using
        (hp.comp u (hconst.prodMk (hd z u).hasFDerivAt)).hasDerivAt
    have hproj (v : ℝ) : P (z, C (z, v)) = v :=
      congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.1) (hRecover z hz v)
    have hid : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
    exact (hid.unique (by simpa only [hproj] using hcomp)).symm
  let S : ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) →
      (ℝ × ℝ) × (ℝ × ℝ) := fun p => (p.1.1, p.2.1)
  let B := S ⁻¹' T.target
  let J : ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ :=
    fun p => fderiv ℝ P (S p) (0, p.2.2)
  let N : ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ := fun p => H (S p)
  have hS : ContDiff ℝ ∞ S := contDiff_fst.fst.prodMk contDiff_snd.fst
  have hB : IsOpen B := T.open_target.preimage hS.continuous
  have hfd : ContinuousOn (fun p => fderiv ℝ P p) T.target :=
    hP.continuousOn_fderiv_of_isOpen T.open_target (by simp)
  have hJ : ContinuousOn J B :=
    (hfd.comp hS.continuous.continuousOn (fun _ hp => hp)).clm_apply
      (continuous_const.prodMk continuous_snd.snd).continuousOn
  have hN : ContinuousOn N B :=
    hH.continuousOn.comp hS.continuous.continuousOn (fun _ hp => hp)
  let W := (B ∩ J ⁻¹' Ioi 0) ∩ (B ∩ N ⁻¹' Ioo (-A) A)
  have hW : IsOpen W :=
    (hJ.isOpen_inter_preimage hB isOpen_Ioi).inter
      (hN.isOpen_inter_preimage hB isOpen_Ioo)
  have hbase (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) :
      ((z, u), (C (z, u), D (z, u))) ∈ W := by
    have hzero : H (z, C (z, u)) = 0 :=
      congrArg (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.2.2) (hRecover z hz u)
    refine ⟨⟨hTarget z hz u, ?_⟩, ⟨hTarget z hz u, ?_⟩⟩
    · change 0 < fderiv ℝ P (z, C (z, u)) (0, D (z, u))
      rw [hcal z hz u]
      norm_num
    · change -A < H (z, C (z, u)) ∧ H (z, C (z, u)) < A
      rw [hzero]
      exact ⟨by linarith, hA⟩
  let M : ℝ := R + 2
  let F : (ℝ × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) :=
    fun p => (p, (C p, D p))
  have hF : Continuous F := continuous_id.prodMk (hC.continuous.prodMk hD.continuous)
  have hcompact : IsCompact (F '' (K ×ˢ Icc (-M) M)) :=
    (hK.prod isCompact_Icc).image hF
  have hinside : F '' (K ×ˢ Icc (-M) M) ⊆ W := by
    rintro q ⟨⟨z, u⟩, ⟨hz, _⟩, rfl⟩
    exact hbase z hz u
  obtain ⟨ε, hε, hthick⟩ := hcompact.exists_thickening_subset_open hW hinside
  obtain ⟨η, hη, hηhalf, hestimate⟩ :=
    exists_uniform_shifted_rounded_sampling_estimates hK (l := -M) (u := M)
      (c := fun z u => C (z, u)) (d := fun z u => D (z, u))
      hC.continuous.continuousOn (fun z _ u _ => hd z u) hD.continuous.continuousOn hε
  refine ⟨η, hη, hηhalf, ?_⟩
  intro a0 h hh hsmall δ hδ hδhalf ρ hρ htail hbound hder
  dsimp only
  let G : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p =>
    roundedVertexPath ρ (fun i : ℤ => C (p.1, a0 + h * i)) ((p.2 - a0) / h)
  have hhalf : h < 1 / 2 := hsmall.trans hηhalf
  have hvertices (i : ℤ) : ContDiff ℝ ∞ (fun z => C (z, a0 + h * i)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_roundedVertexPath hδ hδhalf htail hbound hρ hvertices).comp
      (contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const h))
  have haxis (z : ℝ × ℝ) (u : ℝ) (hu : R + 1 < |u|) : G (z, u) = (u, 0) := by
    apply rounded_affine_grid_axis_of_nearby (fun v => C (z, v)) ρ hh hhalf
    intro v hv
    apply hTail z v
    have hsum : |u| ≤ |v - u| + |v| := by
      simpa only [sub_zero, abs_sub_comm] using (_root_.abs_sub_le u v 0)
    linarith
  have hmem (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) :
      ((z, u), (G (z, u), deriv (fun v => G (z, v)) u)) ∈ W := by
    by_cases hu : u ∈ Icc (-M) M
    · have hclose := hestimate a0 h hh hsmall δ hδ hδhalf ρ
        (hρ.differentiable (by simp)) htail hbound hder z hz u hu
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨F (z, u), ⟨(z, u), ⟨hz, hu⟩, rfl⟩, ?_⟩
      change dist ((z, u), (G (z, u), deriv (fun v => G (z, v)) u))
        ((z, u), (C (z, u), D (z, u))) < ε
      rw [dist_prod_same_left, Prod.dist_eq]
      exact max_lt hclose.1 (by simpa only [dist_eq_norm] using hclose.2)
    · have hlarge : R + 2 < |u| := lt_of_not_ge (fun h => hu (abs_le.mp h))
      have hopen : IsOpen {v : ℝ | R + 1 < |v|} :=
        isOpen_lt continuous_const continuous_abs
      have hn : ∀ᶠ v : ℝ in 𝓝 u, R + 1 < |v| :=
        hopen.mem_nhds (show R + 1 < |u| by linarith)
      have heq : (fun v => G (z, v)) =ᶠ[𝓝 u] (fun v => C (z, v)) := by
        filter_upwards [hn] with v hv
        rw [haxis z v hv, hTail z v (by linarith)]
      have hv : G (z, u) = C (z, u) := heq.eq_of_nhds
      have hdG : deriv (fun v => G (z, v)) u = D (z, u) :=
        heq.deriv_eq.trans (hd z u).deriv
      rw [hv, hdG]
      exact hbase z hz u
  refine ⟨hG, ?_, ?_, ?_⟩
  · intro z u hu
    exact haxis z u (by linarith)
  · intro z hstat u
    exact rounded_affine_grid_axis_of_nearby (fun v => C (z, v)) ρ hh hhalf
      (fun v _ => hstat v)
  · intro z hz u
    have hq := hmem z hz u
    exact ⟨hq.1.1, hq.1.2, abs_lt.mpr hq.2.2⟩

end PoincareConjecture.M25.Topology3D
