import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Minimizing.ExponentialChord
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace Poincare.VolumeComparison

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in

theorem tangentNorm_coordDeriv_eq
    (g : PoincareConjecture.RiemannianMetric n M) {γ : ℝ → M} {I : Set ℝ}
    (hγ : g.IsGeodesicOn γ I) {t : ℝ} (ht : t ∈ I)
    {p : M} (hp : γ t = p) {w : EuclideanSpace ℝ (Fin n)}
    (hd : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u)) w t) :
    g.tangentNorm p w =
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) := by
    rw [hp]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ p)
  have hchain := mfderiv_comp t hc
    ((hγ.contMDiffAt ht).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun L => L (1 : ℝ)) hchain
  change (fderiv ℝ (fun u => extChartAt (𝓡 n) p (γ u)) t) 1 =
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul, hd.deriv] at hv
  have hid : ∀ v : TangentSpace (𝓡 n) (γ t),
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) v = v := by
    rw [hp]
    intro v
    rw [mfderiv_extChartAt_self]
    rfl
  rw [hid] at hv
  unfold PoincareConjecture.RiemannianMetric.tangentNorm
  rw [hv, hp]

omit [T2Space M] in

theorem tangentNorm_eq_of_mem_Icc
    (g : PoincareConjecture.RiemannianMetric n M) {γ : ℝ → M} {a b s t : ℝ}
    (hγ : g.IsGeodesicOn γ (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.tangentNorm (γ s) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1) =
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) := by
  have hh := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hγ.hasDerivAt_tangentNorm_zero hu).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ))) ht hs
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh

omit [T2Space M] in

theorem edist_le_of_geodesic_speed_Icc
    (g : PoincareConjecture.RiemannianMetric n M) {γ : ℝ → M} {a b C s t : ℝ}
    (hγ : g.IsGeodesicOn γ (Icc a b))
    (hC : ∀ u ∈ Icc a b,
      g.tangentNorm (γ u) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1) = C)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    g.edist (γ s) (γ t) ≤ ENNReal.ofReal (|s - t| * C) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hforward : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      g.edist (γ u) (γ v) ≤ ENNReal.ofReal ((v - u) * C) := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu.1 hv.2
    have hd := Manifold.riemannianEDist_le_pathELength
      (hγ.contMDiffOn.mono hsub) rfl rfl huv
    have hl := g.pathELength_eq_of_tangentNorm_eq (fun z hz => hC z (hsub hz))
    change g.edist (γ u) (γ v) ≤ g.pathELength γ u v at hd
    rw [hl, mul_comm, ← ENNReal.ofReal_mul (sub_nonneg.mpr huv)] at hd
    exact hd
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hforward s hs t ht hst
  · simpa only [PoincareConjecture.RiemannianMetric.edist, Manifold.riemannianEDist_comm,
      abs_of_nonneg (sub_nonneg.mpr hts)] using hforward t ht s hs hts

theorem eq_nhds_of_common_minimizing_continuation
    (g : PoincareConjecture.RiemannianMetric n M) (p : M)
    {α η β : ℝ → M}
    (hα : g.IsGeodesicOn α (Icc (0 : ℝ) 1))
    (hη : g.IsGeodesicOn η (Icc (0 : ℝ) 1))
    (hβ : g.IsGeodesicOn β (Icc (0 : ℝ) 1))
    (hα0 : α 0 = p) (hη0 : η 0 = p) (hβ0 : β 0 = p)
    {u v w : EuclideanSpace ℝ (Fin n)}
    (hαv : HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) u 0)
    (hηv : HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0)
    (hβv : HasDerivAt (fun t => extChartAt (𝓡 n) p (β t)) w 0)
    (hu : 0 < g.tangentNorm p u) (hw : 0 < g.tangentNorm p w)
    (huv : g.tangentNorm p u = g.tangentNorm p v)
    (hαupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p u))
    (hηupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p v))
    (hβupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (β s) (β t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w))
    (hend : α 1 = η 1)
    (hdist : g.edist (α 1) (β 1) =
      ENNReal.ofReal (g.tangentNorm p u + g.tangentNorm p w)) :
    ∀ t ∈ Icc (0 : ℝ) 1, α =ᶠ[𝓝 t] η := by
  have h₁ := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics p
    hα hβ hα0 hβ0 hαv hβv hu hw hαupper hβupper hdist
  have h₂ := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics p
    hη hβ hη0 hβ0 hηv hβv (huv ▸ hu) hw hηupper hβupper
    (by simpa only [← hend, ← huv] using hdist)
  have huv' : u = v := by
    have hh := neg_injective (h₁.symm.trans h₂)
    rw [← huv] at hh
    exact (smul_right_injective _ (inv_ne_zero hu.ne')) hh
  apply hα.eq_nhds_on_of_initial_data hη (convex_Icc _ _).isPreconnected
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) p
    (by simpa only [hα0] using mem_extChartAt_source p)
    (hα0.trans hη0.symm)
  exact hαv.deriv.trans (huv'.trans hηv.deriv.symm)

omit [T2Space M] in
private theorem tangentNorm_smul (g : PoincareConjecture.RiemannianMetric n M)
    (p : M) (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm p (a • v) = |a| * g.tangentNorm p v := by
  simp only [PoincareConjecture.RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem eq_nhds_of_minimizing_extension
    (g : PoincareConjecture.RiemannianMetric n M) {γ η : ℝ → M} {q C : ℝ}
    (hq : 1 < q) (hC : 0 < C)
    (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) q))
    (hη : g.IsGeodesicOn η (Icc (0 : ℝ) 1))
    (hstart : γ 0 = η 0) (hend : γ 1 = η 1)
    (hγspeed : ∀ t ∈ Icc (0 : ℝ) q,
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = C)
    (hηspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (η t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η t 1) = C)
    (hdist : g.edist (γ 0) (γ q) = ENNReal.ofReal (q * C)) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ =ᶠ[𝓝 t] η := by
  let p := γ 1
  let c := extChartAt (𝓡 n) p
  let u := deriv (fun t => c (γ t)) 1
  let v := deriv (fun t => c (η t)) 1
  have h1q : (1 : ℝ) ∈ Icc (0 : ℝ) q := ⟨zero_le_one, hq.le⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hu : HasDerivAt (fun t => c (γ t)) u 1 :=
    (hγ.hasDerivAt_chart_at h1q p (mem_extChartAt_source p)).1
  have hv : HasDerivAt (fun t => c (η t)) v 1 :=
    (hη.hasDerivAt_chart_at h1 p (by rw [← hend]; exact mem_extChartAt_source p)).1
  have huC : g.tangentNorm p u = C :=
    (tangentNorm_coordDeriv_eq g hγ h1q rfl hu).trans (hγspeed 1 h1q)
  have hvC : g.tangentNorm p v = C :=
    (tangentNorm_coordDeriv_eq g hη h1 hend.symm hv).trans (hηspeed 1 h1)
  let α := fun t : ℝ => γ ((-1) * t + 1)
  let ξ := fun t : ℝ => η ((-1) * t + 1)
  let β := fun t : ℝ => γ ((q - 1) * t + 1)
  have hrev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (-1) * t + 1 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hfwd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (q - 1) * t + 1 ∈ Icc (0 : ℝ) q := by
    have hlo := mul_nonneg (sub_pos.mpr hq).le ht.1
    have hhi := mul_le_mul_of_nonneg_left ht.2 (sub_pos.mpr hq).le
    constructor <;> linarith
  have hα : g.IsGeodesicOn α (Icc (0 : ℝ) 1) := fun t ht =>
    hγ.comp_affine (-1) 1 t ⟨(hrev t ht).1, (hrev t ht).2.trans hq.le⟩
  have hξ : g.IsGeodesicOn ξ (Icc (0 : ℝ) 1) := fun t ht =>
    hη.comp_affine (-1) 1 t (hrev t ht)
  have hβ : g.IsGeodesicOn β (Icc (0 : ℝ) 1) := fun t ht =>
    hγ.comp_affine (q - 1) 1 t (hfwd t ht)
  have hdu : HasDerivAt (fun t => c (α t)) ((-1 : ℝ) • u) 0 := by
    have hu' : HasDerivAt (fun t => c (γ t)) u ((-1 : ℝ) * 0 + 1) := by simpa using hu
    simpa only [α, Function.comp_def, mul_one, id_eq] using!
      hu'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (-1)).add_const 1)
  have hdv : HasDerivAt (fun t => c (ξ t)) ((-1 : ℝ) • v) 0 := by
    have hv' : HasDerivAt (fun t => c (η t)) v ((-1 : ℝ) * 0 + 1) := by simpa using hv
    simpa only [ξ, Function.comp_def, mul_one, id_eq] using!
      hv'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (-1)).add_const 1)
  have hdw : HasDerivAt (fun t => c (β t)) ((q - 1) • u) 0 := by
    have hu' : HasDerivAt (fun t => c (γ t)) u ((q - 1) * 0 + 1) := by simpa using hu
    simpa only [β, Function.comp_def, mul_one, id_eq] using!
      hu'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (q - 1)).add_const 1)
  have hnu : g.tangentNorm p ((-1 : ℝ) • u) = C := by
    rw [tangentNorm_smul, huC]; norm_num
  have hnv : g.tangentNorm p ((-1 : ℝ) • v) = C := by
    rw [tangentNorm_smul, hvC]; norm_num
  have hnw : g.tangentNorm p ((q - 1) • u) = (q - 1) * C := by
    rw [tangentNorm_smul, abs_of_pos (sub_pos.mpr hq), huC]
  have hαup : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * C) := by
    intro s hs t ht
    have hh := edist_le_of_geodesic_speed_Icc g hγ hγspeed
      ⟨(hrev s hs).1, (hrev s hs).2.trans hq.le⟩
      ⟨(hrev t ht).1, (hrev t ht).2.trans hq.le⟩
    have heq : -1 * s + 1 - (-1 * t + 1) = -(s - t) := by ring
    simpa only [α, heq, abs_neg] using hh
  have hξup : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (ξ s) (ξ t) ≤ ENNReal.ofReal (|s - t| * C) := by
    intro s hs t ht
    have hh := edist_le_of_geodesic_speed_Icc g hη hηspeed (hrev s hs) (hrev t ht)
    have heq : -1 * s + 1 - (-1 * t + 1) = -(s - t) := by ring
    simpa only [ξ, heq, abs_neg] using hh
  have hβup : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (β s) (β t) ≤ ENNReal.ofReal (|s - t| * ((q - 1) * C)) := by
    intro s hs t ht
    have hh := edist_le_of_geodesic_speed_Icc g hγ hγspeed (hfwd s hs) (hfwd t ht)
    have heq : (q - 1) * s + 1 - ((q - 1) * t + 1) = (q - 1) * (s - t) := by ring
    simpa only [β, heq, abs_mul, abs_of_pos (sub_pos.mpr hq),
      mul_left_comm, mul_assoc] using hh
  have heq := eq_nhds_of_common_minimizing_continuation g p hα hξ hβ
    (by simp [α, p]) (by simp [ξ, p, ← hend]) (by simp [β, p])
    hdu hdv hdw (by simpa only [hnu] using hC)
    (by simpa only [hnw] using mul_pos (sub_pos.mpr hq) hC)
    (hnu.trans hnv.symm)
    (by simpa only [hnu] using hαup)
    (by simpa only [hnv] using hξup)
    (by simpa only [hnw] using hβup)
    (by simpa [α, ξ] using hstart)
    (by
      rw [hnu, hnw]
      simpa only [α, β, mul_one, neg_add_cancel, sub_add_cancel,
        show C + (q - 1) * C = q * C by ring] using hdist)
  have huv : u = v := by
    have hh := ((heq 0 (by simp)).fun_comp c).deriv_eq
    change deriv (fun t => c (α t)) 0 = deriv (fun t => c (ξ t)) 0 at hh
    rw [hdu.deriv, hdv.deriv] at hh
    simpa only [neg_one_smul, neg_inj] using hh
  have hγ' : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) :=
    fun t ht => hγ t ⟨ht.1, ht.2.trans hq.le⟩
  exact hγ'.eq_nhds_on_of_initial_data hη (convex_Icc _ _).isPreconnected h1 p
    (mem_extChartAt_source p) hend (hu.deriv.trans (huv.trans hv.deriv.symm))

end Poincare.VolumeComparison
