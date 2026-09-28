import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.IsometryRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

private theorem tangentNorm_smul_nonneg
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (p v : EuclideanSpace ℝ (Fin n)) {a : ℝ} (ha : 0 ≤ a) :
    g.tangentNorm p (a • v) = a * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

private theorem minimizing_speed
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hγ : g.IsGeodesicOn γ (Ioo (-1 : ℝ) 2))
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 2) :
    g.tangentNorm (γ t) (deriv γ t) = (g.edist (γ 0) (γ 1)).toReal := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  have hd (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 2) :
      HasDerivAt (fun s => extChartAt (𝓡 n) (γ u) (γ s)) (deriv γ u) u := by
    simpa using (hγ.hasDerivAt_chart_at hu (γ u) (mem_extChartAt_source _)).1
  have hγ' : g.IsGeodesicOn γ (Ioo (-1 : ℝ) (1 + 1)) := by norm_num; exact hγ
  have hs := hγ'.initial_tangentNorm_eq_of_edist_segment (ε := 1)
    (by norm_num) rfl (hd 0 h0) hmin
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm (by norm_num)
  have hnorm (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 2) :
      g.tangentNorm (γ u) (deriv γ u) = C := by
    convert! hC u hu using 1; simp only [mfderiv_eq_fderiv, deriv]
    rfl
  have hs' := congrArg ENNReal.toReal hs
  rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0) (deriv γ 0) from
    Real.sqrt_nonneg _)] at hs'
  exact (hnorm t ht).trans ((hnorm 0 h0).symm.trans hs')

theorem tangentNorm_fderiv_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (v : EuclideanSpace ℝ (Fin n)) :
    h.tangentNorm (f p) (fderiv ℝ f p v) = g.tangentNorm p v := by
  obtain ⟨ε, hε, _, γ, hγ, hγ0, hγv⟩ := g.exists_geodesic_initial_data p v
  have hv : HasDerivAt γ v 0 := by simpa using hγv
  have hJ : IsOpen (Ioo (-ε) ε ∩ γ ⁻¹' U) :=
    (hγ.contMDiffOn.continuousOn).isOpen_inter_preimage isOpen_Ioo hU
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε ∩ γ ⁻¹' U :=
    ⟨⟨by linarith, hε⟩, by simpa only [mem_preimage, hγ0] using hp⟩
  have hγ' : g.IsGeodesicOn γ (Ioo (-ε) ε ∩ γ ⁻¹' U) := fun t ht => hγ t ht.1
  obtain ⟨δ, hδ, hsub, hη, hmin⟩ := hγ'.exists_minimizing_affine_neighborhood hJ h0
  let η := fun t => γ (2 * δ * t + (0 - δ))
  have hηU : MapsTo η (Ioo (-1 : ℝ) 2) U := by
    intro t ht
    apply (hsub (show 2 * δ * t + (0 - δ) ∈ Ioo (0 - 3 * δ) (0 + 3 * δ) from ?_)).2
    constructor <;> nlinarith [ht.1, ht.2]
  have hη' : h.IsGeodesicOn (f ∘ η) (Ioo (-1 : ℝ) 2) :=
    (hη.comp_of_edist_eq h hdist isOpen_Ioo hηU).1
  have hmin' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      h.edist ((f ∘ η) s) ((f ∘ η) t) = ENNReal.ofReal |s - t| *
        h.edist ((f ∘ η) 0) ((f ∘ η) 1) := by
    intro s hs t ht
    simp only [Function.comp_apply]
    rw [hdist _ (hηU ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      _ (hηU ⟨by linarith [ht.1], by linarith [ht.2]⟩),
      hdist _ (hηU (by norm_num)) _ (hηU (by norm_num))]
    exact hmin s hs t ht
  have hηhalf : η (1 / 2) = p := by dsimp [η]; convert hγ0 using 1; congr 1; ring
  have hdη : HasDerivAt η ((2 * δ) • v) (1 / 2) := by
    have hv' : HasDerivAt γ v (2 * δ * (1 / 2) + (0 - δ)) := by
      convert hv using 1; ring
    have hh := hv'.scomp (1 / 2)
      (((hasDerivAt_id (1 / 2)).const_mul (2 * δ)).add_const (0 - δ))
    convert! hh using 1; simp only [mul_one]
  have hf := ((g.contDiffOn_of_edist_eq h hU hdist).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdcomp : HasDerivAt (f ∘ η) ((2 * δ) • fderiv ℝ f p v) (1 / 2) := by
    have hf' : HasFDerivAt f (fderiv ℝ f p) (η (1 / 2)) := by
      rw [hηhalf]; exact hf.hasFDerivAt
    have hh := (hf'.comp_hasDerivAt (1 / 2) hdη)
    simpa only [hηhalf, map_smul] using hh
  have hs := minimizing_speed (γ := η) hη (by exact hmin) (t := 1 / 2) (by norm_num)
  have hs' := minimizing_speed hη' hmin' (t := 1 / 2) (by norm_num)
  simp only [tangentNorm] at hs hs'
  rw [hdη.deriv, hηhalf] at hs
  change g.tangentNorm p ((2 * δ) • v) = _ at hs
  rw [tangentNorm_smul_nonneg g p v (by positivity)] at hs
  rw [hdcomp.deriv, Function.comp_apply, hηhalf] at hs'
  change h.tangentNorm (f p) ((2 * δ) • fderiv ℝ f p v) = _ at hs'
  rw [
    tangentNorm_smul_nonneg h (f p) _ (by positivity),
    Function.comp_apply, Function.comp_apply,
    hdist _ (hηU (by norm_num)) _ (hηU (by norm_num))] at hs'
  exact (mul_left_cancel₀ (by positivity : (2 * δ : ℝ) ≠ 0)) (hs'.trans hs.symm)

theorem inner_fderiv_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U)
    (v w : EuclideanSpace ℝ (Fin n)) :
    h.inner (f p) (fderiv ℝ f p v) (fderiv ℝ f p w) = g.inner p v w := by
  have hnonneg {d : ℕ} (a : RiemannianMetric d (EuclideanSpace ℝ (Fin d)))
      (x z : EuclideanSpace ℝ (Fin d)) : 0 ≤ a.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (a.pos x z hz).le
  have hdiag (z : EuclideanSpace ℝ (Fin n)) :
      h.inner (f p) (fderiv ℝ f p z) (fderiv ℝ f p z) = g.inner p z z := by
    have hh := congrArg (fun a : ℝ => a ^ 2)
      (g.tangentNorm_fderiv_of_edist_eq h hU hdist hp z)
    simpa only [tangentNorm, Real.sq_sqrt (hnonneg h _ _),
      Real.sq_sqrt (hnonneg g _ _)] using hh
  have hh := hdiag (v + w)
  simp only [map_add, add_apply] at hh
  rw [h.symm (f p) (fderiv ℝ f p w) (fderiv ℝ f p v), g.symm p w v] at hh
  linarith [hdiag v, hdiag w]

theorem smooth_isometric_charts_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source, h.edist (e x) (e y) = g.edist x y) :
    ContMDiffOn (𝓡 n) (𝓡 m) ∞ e e.source ∧
      ContMDiffOn (𝓡 m) (𝓡 n) ∞ e.symm e.target ∧
      ∀ p ∈ e.source, ∀ v w : EuclideanSpace ℝ (Fin n),
        h.inner (e p) (mfderiv (𝓡 n) (𝓡 m) e p v)
          (mfderiv (𝓡 n) (𝓡 m) e p w) = g.inner p v w := by
  refine ⟨(g.contDiffOn_of_edist_eq h e.open_source hdist).contMDiffOn, ?_, ?_⟩
  · apply ContDiffOn.contMDiffOn
    apply h.contDiffOn_of_edist_eq g e.open_target
    intro x hx y hy
    simpa only [e.right_inv hx, e.right_inv hy] using
      (hdist (e.symm x) (e.map_target hx) (e.symm y) (e.map_target hy)).symm
  · intro p hp v w
    convert! g.inner_fderiv_of_edist_eq h e.open_source hdist hp v w using 1
    simp only [mfderiv_eq_fderiv]
    rfl

end PoincareConjecture.RiemannianMetric
