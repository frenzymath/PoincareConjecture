import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Minimizing.ExponentialChord
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Geodesic

















noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]


theorem continuous_toReal_displacement (g : RiemannianMetric n M)
    {F : M → M} (hF : Continuous F) :
    Continuous (fun x => (g.edist x (F x)).toReal) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : ContinuousAt (fun y => g.edist y (F y)) x :=
    (continuous_id.edist hF).continuousAt
  exact ContinuousAt.comp (f := fun y => g.edist y (F y))
    (ENNReal.continuousAt_toReal (g.edist_ne_top x (F x))) hc


theorem exists_positive_minimum_displacement [CompactSpace M] [Nonempty M]
    (g : RiemannianMetric n M) {F : M → M} (hF : Continuous F)
    (hfree : ∀ x, F x ≠ x) :
    ∃ p : M, 0 < (g.edist p (F p)).toReal ∧
      ∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal := by
  obtain ⟨p, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (univ : Set M).Nonempty from ⟨Classical.choice inferInstance, mem_univ _⟩)
    (g.continuous_toReal_displacement hF).continuousOn
  refine ⟨p, ?_, fun x => hmin (mem_univ x)⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact ENNReal.toReal_pos (ne_of_gt (edist_pos.mpr (hfree p).symm))
    (g.edist_ne_top p (F p))



theorem exists_minimum_displacement_geodesic [CompactSpace M] [Nonempty M]
    (g : RiemannianMetric n M) {F : M → M} (hF : Continuous F)
    (hfree : ∀ x, F x ≠ x) :
    ∃ p : M, 0 < (g.edist p (F p)).toReal ∧
      (∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧ γ 1 = F p ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p (F p) := by
  obtain ⟨p, hp, hmin⟩ := g.exists_positive_minimum_displacement hF hfree
  have hc : MetricComplete g := by
    unfold MetricComplete
    infer_instance
  exact ⟨p, hp, hmin, g.exists_minimizing_geodesic_of_metricComplete hc p (F p)⟩

omit [PreconnectedSpace M] in
private theorem initial_norm_of_distance_formula
    (g : RiemannianMetric n M) {γ : ℝ → M} {ε C : ℝ} (hε : 0 < ε)
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) {p : M} (hγ0 : γ 0 = p)
    {v : EuclideanSpace ℝ (Fin n)}
    (hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0)
    (hC : 0 ≤ C)
    (hdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal (|s - t| * C)) :
    g.tangentNorm p v = C := by
  have h01 : g.edist p (γ 1) = ENNReal.ofReal C := by
    simpa only [hγ0, zero_sub, abs_neg, abs_one, one_mul] using
      hdist 0 (by simp) 1 (by simp)
  have hspeed := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv
    (q := γ 1) (fun s hs t ht => by
      rw [hdist s hs t ht, h01, ENNReal.ofReal_mul (abs_nonneg _)])
  rw [h01] at hspeed
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm p v from Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal hC] using congrArg ENNReal.toReal hspeed



theorem midpoint_displacement_eq_of_minimizing
    (g : RiemannianMetric n M) {F : M → M}
    (hF : ∀ x y, g.edist (F x) (F y) = g.edist x y)
    {p : M} {γ : ℝ → M} (hγ0 : γ 0 = p) (hγ1 : γ 1 = F p)
    (hmin : ∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p (F p)) :
    g.edist (γ (1 / 2)) (F (γ (1 / 2))) = g.edist p (F p) := by
  have hleg₁ : (g.edist (γ (1 / 2)) (F p)).toReal =
      (g.edist p (F p)).toReal / 2 := by
    have hh := hseg (1 / 2) (by norm_num) 1 (by simp)
    rw [hγ1] at hh
    rw [hh, ENNReal.toReal_mul]
    norm_num
    ring
  have hleg₂ : (g.edist (F p) (F (γ (1 / 2)))).toReal =
      (g.edist p (F p)).toReal / 2 := by
    rw [hF]
    have hh := hseg 0 (by simp) (1 / 2) (by norm_num)
    rw [hγ0] at hh
    rw [hh, ENNReal.toReal_mul]
    norm_num
    ring
  have hreal : (g.edist (γ (1 / 2)) (F (γ (1 / 2)))).toReal =
      (g.edist p (F p)).toReal := by
    apply le_antisymm
    · have hh := g.toReal_edist_triangle (γ (1 / 2)) (F p) (F (γ (1 / 2)))
      rw [hleg₁, hleg₂] at hh
      linarith
    · exact hmin _
  rw [← ENNReal.ofReal_toReal (g.edist_ne_top (γ (1 / 2)) (F (γ (1 / 2)))),
    ← ENNReal.ofReal_toReal (g.edist_ne_top p (F p)), hreal]




theorem endpoint_chart_velocity_eq_of_minimum_displacement
    (g : RiemannianMetric n M) (F : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {p : M} {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = F p)
    (hpos : 0 < (g.edist p (F p)).toReal)
    (hmin : ∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p (F p)) :
    deriv (fun t => extChartAt (𝓡 n) (F p) (F (γ t))) 0 =
      deriv (fun t => extChartAt (𝓡 n) (F p) (γ t)) 1 := by
  let L := (g.edist p (F p)).toReal
  have hL : 0 < L := hpos
  have hdist : g.edist p (F p) = ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal (g.edist_ne_top _ _)).symm
  have hFi (x y : M) : g.edist (F x) (F y) = g.edist x y :=
    (g.edist_diffeomorph g F hinner x y).symm
  have hFγ : g.IsGeodesicOn (F ∘ γ) (Ioo (-ε) (1 + ε)) :=
    hγ.comp_local_isometry_manifold isOpen_univ F.contMDiff.contMDiffOn
      (fun x _ v w => hinner x v w) (fun _ _ => mem_univ _)
  let α := fun t : ℝ => γ ((-1 / 2) * t + 1)
  let β := fun t : ℝ => F (γ ((1 / 2) * t))
  have hα : g.IsGeodesicOn α (Ioo (-ε) (1 + ε)) := by
    intro t ht
    apply hγ.comp_affine (-1 / 2) 1
    constructor <;> linarith [ht.1, ht.2]
  have hβ : g.IsGeodesicOn β (Ioo (-ε) (1 + ε)) := by
    intro t ht
    apply hFγ.comp_mul (1 / 2)
    constructor <;> linarith [ht.1, ht.2]
  have hα0 : α 0 = F p := by simp [α, hγ1]
  have hβ0 : β 0 = F p := by simp [β, hγ0]
  have hback (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (-1 / 2) * t + 1 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hfwd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 / 2) * t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hαdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (α s) (α t) = ENNReal.ofReal (|s - t| * (L / 2)) := by
    intro s hs t ht
    rw [hseg _ (hback s hs) _ (hback t ht), hdist,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show (-1 / 2) * s + 1 - ((-1 / 2) * t + 1) =
      (-1 / 2) * (s - t) by ring, abs_mul]
    norm_num
    ring
  have hβdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (β s) (β t) = ENNReal.ofReal (|s - t| * (L / 2)) := by
    intro s hs t ht
    change g.edist (F (γ ((1 / 2) * s))) (F (γ ((1 / 2) * t))) = _
    rw [hFi, hseg _ (hfwd s hs) _ (hfwd t ht), hdist,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [← mul_sub, abs_mul]
    norm_num
    ring
  let u := deriv (fun t => extChartAt (𝓡 n) (F p) (γ t)) 1
  let v := deriv (fun t => extChartAt (𝓡 n) (F p) (F (γ t))) 0
  have hu := (hγ.hasDerivAt_chart_at (show (1 : ℝ) ∈ Ioo (-ε) (1 + ε) by
    constructor <;> linarith) (F p) (by simp [hγ1])).1
  have hv := (hFγ.hasDerivAt_chart_at (show (0 : ℝ) ∈ Ioo (-ε) (1 + ε) by
    constructor <;> linarith) (F p) (by
      simp [hγ0])).1
  have hαv : HasDerivAt (fun t => extChartAt (𝓡 n) (F p) (α t))
      ((-1 / 2 : ℝ) • u) 0 := by
    have hu' : HasDerivAt (fun t => extChartAt (𝓡 n) (F p) (γ t)) u
        ((-1 / 2) * 0 + 1) := by simpa only [mul_zero, zero_add] using hu
    simpa! only [α, Function.comp_def, mul_one, id_eq] using
      hu'.scomp 0 (((hasDerivAt_id (0 : ℝ)).const_mul (-1 / 2)).add_const 1)
  have hβv : HasDerivAt (fun t => extChartAt (𝓡 n) (F p) (β t))
      ((1 / 2 : ℝ) • v) 0 := by
    have hv' : HasDerivAt (fun t => extChartAt (𝓡 n) (F p) (F (γ t))) v
        ((1 / 2) * 0) := by simpa only [mul_zero, v, Function.comp_def] using hv
    simpa! only [β, Function.comp_def, mul_one, id_eq] using
      hv'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul (1 / 2))
  have hAnorm := initial_norm_of_distance_formula g hε hα hα0 hαv
    (by positivity : 0 ≤ L / 2) hαdist
  have hBnorm := initial_norm_of_distance_formula g hε hβ hβ0 hβv
    (by positivity : 0 ≤ L / 2) hβdist
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcorner := g.normalized_initial_eq_neg_of_minimizing_broken_geodesics (F p)
    (fun t ht => hα t (hI ht)) (fun t ht => hβ t (hI ht)) hα0 hβ0 hαv hβv
    (by rw [hAnorm]; positivity) (by rw [hBnorm]; positivity)
    (fun s hs t ht => (hαdist s hs t ht).trans_le (by rw [hAnorm]))
    (fun s hs t ht => (hβdist s hs t ht).trans_le (by rw [hBnorm])) (by
      rw [show α 1 = γ (1 / 2) by dsimp [α]; congr 1; norm_num,
        show β 1 = F (γ (1 / 2)) by simp only [β, mul_one],
        g.midpoint_displacement_eq_of_minimizing hFi hγ0 hγ1 hmin hseg,
        hAnorm, hBnorm, hdist]
      congr 1
      ring)
  rw [hAnorm, hBnorm, smul_smul, smul_smul, ← neg_smul] at hcorner
  have hscalar : -((L / 2)⁻¹ * (-1 / 2)) = (L / 2)⁻¹ * (1 / 2) := by ring
  rw [hscalar] at hcorner
  exact (smul_right_injective _ (mul_ne_zero (inv_ne_zero (ne_of_gt (by positivity :
    0 < L / 2))) (by norm_num : (1 / 2 : ℝ) ≠ 0))) hcorner

omit [T3Space M] [PreconnectedSpace M] in
private theorem deriv_chart_eq_velocity {γ : ℝ → M} {t : ℝ} {p : M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ t) (hp : γ t = p) :
    deriv (fun s => extChartAt (𝓡 n) p (γ s)) t =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) := by
    rw [hp]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ p)
  have hchain := mfderiv_comp t hc hγ
  rw [mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun L => L (1 : ℝ)) hchain
  change (fderiv ℝ (fun s => extChartAt (𝓡 n) p (γ s)) t) 1 =
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul] at hv
  have hid : ∀ v : TangentSpace (𝓡 n) (γ t),
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ t) v = v := by
    rw [hp]
    intro v
    rw [mfderiv_extChartAt_self]
    rfl
  rw [hid] at hv
  exact hv



theorem endpoint_velocity_eq_of_minimum_displacement
    (g : RiemannianMetric n M) (F : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    {p : M} {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = F p)
    (hpos : 0 < (g.edist p (F p)).toReal)
    (hmin : ∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p (F p)) :
    mfderiv (𝓡 n) (𝓡 n) F p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have h1 : (1 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  have hd0 := (hγ.contMDiffAt h0).mdifferentiableAt (by simp)
  have hd1 := (hγ.contMDiffAt h1).mdifferentiableAt (by simp)
  have hdF := F.mdifferentiable (by simp) (γ 0)
  have hpush := congrArg (fun L => L (1 : ℝ)) (mfderiv_comp 0 hdF hd0)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (F ∘ γ) 0 1 =
    mfderiv (𝓡 n) (𝓡 n) F (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at hpush
  rw [hγ0] at hpush
  calc
    _ = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (F ∘ γ) 0 1 := hpush.symm
    _ = deriv (fun t => extChartAt (𝓡 n) (F p) (F (γ t))) 0 :=
      (deriv_chart_eq_velocity (hdF.comp 0 hd0) (by simp [hγ0])).symm
    _ = deriv (fun t => extChartAt (𝓡 n) (F p) (γ t)) 1 :=
      g.endpoint_chart_velocity_eq_of_minimum_displacement F hinner hε hγ
        hγ0 hγ1 hpos hmin hseg
    _ = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := deriv_chart_eq_velocity hd1 hγ1



theorem exists_minimum_displacement_geodesic_with_matched_velocity
    [CompactSpace M] [Nonempty M]
    (g : RiemannianMetric n M) (F : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ M)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = g.inner (F x)
        (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w))
    (hfree : ∀ x, F x ≠ x) :
    ∃ p : M, 0 < (g.edist p (F p)).toReal ∧
      (∀ x : M, (g.edist p (F p)).toReal ≤ (g.edist x (F x)).toReal) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧ γ 1 = F p ∧
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p (F p)) ∧
        mfderiv (𝓡 n) (𝓡 n) F p (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) =
          mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 1 1 := by
  obtain ⟨p, hpos, hmin, ε, hε, γ, hγ, hγ0, hγ1, hseg⟩ :=
    g.exists_minimum_displacement_geodesic F.continuous hfree
  exact ⟨p, hpos, hmin, ε, hε, γ, hγ, hγ0, hγ1, hseg,
    g.endpoint_velocity_eq_of_minimum_displacement F hinner hε hγ
      hγ0 hγ1 hpos hmin hseg⟩

end PoincareConjecture.RiemannianMetric
