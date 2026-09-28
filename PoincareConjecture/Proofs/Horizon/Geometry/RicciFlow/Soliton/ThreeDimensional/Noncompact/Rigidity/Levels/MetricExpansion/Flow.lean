import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Expansion








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open Poincare.Geometry.Riemannian.Convexity
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem inner_connection_normalizedGradient_of_tangent
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0)
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0) :
    g.inner x (D.connection (D.normalizedGradient f) x v) v =
      D.hessian f x v v / g.inner x (D.gradient f x) (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hpair : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  have hinv : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y ↦ (g.inner y (D.gradient f y) (D.gradient f y))⁻¹) x :=
    (differentiableAt_inv hregular).mdifferentiableAt.comp x hpair
  unfold normalizedGradient
  rw [inner_connection_smul_gradient_of_tangent D hf hinv v hv]
  ring



theorem inner_connection_normalizedGradient_nonneg
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : 0 < g.inner x (D.gradient f x) (D.gradient f x))
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0)
    (hhess : 0 ≤ D.hessian f x v v) :
    0 ≤ g.inner x (D.connection (D.normalizedGradient f) x v) v := by
  rw [D.inner_connection_normalizedGradient_of_tangent hf hregular.ne' v hv]
  exact div_nonneg hhess hregular.le

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem hasDerivAt_normalizedGradient_flow_squared_length
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {t : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : ContDiffAt ℝ ∞ q (t, x))
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (t, x)))
    (hregular : g.inner (q (t, x)) (D.gradient f (q (t, x)))
      (D.gradient f (q (t, x))) ≠ 0)
    (htime : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ q (s, y))
      (D.normalizedGradient f (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n))
    (htangent : mvfderiv (𝓡 n) f (q (t, x))
      (fderiv ℝ (fun y ↦ q (t, y)) x v) = 0) :
    let w := fderiv ℝ (fun y ↦ q (t, y)) x v
    HasDerivAt (fun s ↦ g.inner (q (s, x))
      (fderiv ℝ (fun y ↦ q (s, y)) x v)
      (fderiv ℝ (fun y ↦ q (s, y)) x v))
      (2 * D.hessian f (q (t, x)) w w /
        g.inner (q (t, x)) (D.gradient f (q (t, x))) (D.gradient f (q (t, x)))) t := by
  have hfield : DifferentiableAt ℝ (D.normalizedGradient f) (q (t, x)) := by
    have heq : D.normalizedGradient f = fun z ↦ -normalizedNegGradient D f z := by
      funext z
      simp only [normalizedGradient, normalizedNegGradient, neg_smul, neg_neg]
    rw [heq]
    exact (differentiableAt_normalizedNegGradient D hf hregular).neg
  have h := hasDerivAt_flow_squared_length D hq hfield htime v
  dsimp only at h ⊢
  rw [D.inner_connection_normalizedGradient_of_tangent hf hregular _ htangent] at h
  convert! h using 1
  ring

private theorem comp_normalizedGradient_eq_add
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (γ t))
    (hregular : ∀ t ∈ Icc a b,
      g.inner (γ t) (D.gradient f (γ t)) (D.gradient f (γ t)) ≠ 0)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (D.normalizedGradient f (γ t)) t) :
    ∀ t ∈ Icc a b, f (γ t) = f (γ a) + (t - a) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (f ∘ γ) 1 t := by
    have hcomp := ((contMDiffAt_iff_contDiffAt.mp (hf t ht)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t (hγ t ht)
    have he : mvfderiv (𝓡 n) f (γ t) (D.normalizedGradient f (γ t)) = 1 := by
      simp only [normalizedGradient, map_smul, smul_eq_mul, ← D.inner_gradient]
      exact inv_mul_cancel₀ (hregular t ht)
    have he' : fderiv ℝ f (γ t) (D.normalizedGradient f (γ t)) = 1 := by
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at he
      convert! he using 1
    exact hcomp.congr_deriv he'
  have hl (t : ℝ) : HasDerivAt (fun s ↦ f (γ a) + (s - a)) 1 t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_add (f (γ a))
  exact eq_of_has_deriv_right_eq
    (fun t ht ↦ (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t _ ↦ (hl t).hasDerivWithinAt)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hl t).continuousAt.continuousWithinAt) (by simp)



theorem normalizedGradient_flow_preserves_level_differential
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ q (t, x))
    (hf : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (t, y)))
    (hregular : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      g.inner (q (t, y)) (D.gradient f (q (t, y))) (D.gradient f (q (t, y))) ≠ 0)
    (htime : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ q (s, y))
      (D.normalizedGradient f (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : t ∈ Icc a b) :
    mvfderiv (𝓡 n) f (q (t, x)) (fderiv ℝ (fun y ↦ q (t, y)) x v) =
      mvfderiv (𝓡 n) f (q (a, x)) (fderiv ℝ (fun y ↦ q (a, y)) x v) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have he : (fun y ↦ f (q (t, y))) =ᶠ[𝓝 x]
      fun y ↦ f (q (a, y)) + (t - a) := by
    filter_upwards [hf, hregular, htime] with y hy hr hytime
    exact comp_normalizedGradient_eq_add D hy hr hytime t ht
  have hqd (s : ℝ) (hs : s ∈ Icc a b) :
      DifferentiableAt ℝ (fun y ↦ q (s, y)) x :=
    ((hq s hs).differentiableAt (by simp)).comp x
      (differentiableAt_const s |>.prodMk differentiableAt_id)
  have hfd (s : ℝ) (hs : s ∈ Icc a b) : DifferentiableAt ℝ f (q (s, x)) :=
    (contMDiffAt_iff_contDiffAt.mp (hf.self_of_nhds s hs)).differentiableAt (by simp)
  have hleft := (hfd t ht).hasFDerivAt.comp x (hqd t ht).hasFDerivAt
  have hright := ((hfd a ha).hasFDerivAt.comp x (hqd a ha).hasFDerivAt).add_const (t - a)
  have hd := congrArg (fun A ↦ A v) (hleft.unique (hright.congr_of_eventuallyEq he))
  simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  convert! hd using 1



theorem normalizedGradient_flow_squared_length_monotone
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ q (t, x))
    (hf : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (q (t, y)))
    (hregular : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      0 < g.inner (q (t, y)) (D.gradient f (q (t, y))) (D.gradient f (q (t, y))))
    (htime : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ q (s, y))
      (D.normalizedGradient f (q (t, y))) t)
    (v : EuclideanSpace ℝ (Fin n))
    (hinitial : mvfderiv (𝓡 n) f (q (a, x))
      (fderiv ℝ (fun y ↦ q (a, y)) x v) = 0)
    (hhess : ∀ t ∈ Icc a b, ∀ w, mvfderiv (𝓡 n) f (q (t, x)) w = 0 →
      0 ≤ D.hessian f (q (t, x)) w w) :
    MonotoneOn (fun t ↦ g.inner (q (t, x))
      (fderiv ℝ (fun y ↦ q (t, y)) x v)
      (fderiv ℝ (fun y ↦ q (t, y)) x v)) (Icc a b) := by
  have htan (t : ℝ) (ht : t ∈ Icc a b) : mvfderiv (𝓡 n) f (q (t, x))
      (fderiv ℝ (fun y ↦ q (t, y)) x v) = 0 :=
    (D.normalizedGradient_flow_preserves_level_differential hq hf
      (hregular.mono fun y hy s hs ↦ (hy s hs).ne') htime v t ht).trans hinitial
  have hd (t : ℝ) (ht : t ∈ Icc a b) :=
    D.hasDerivAt_normalizedGradient_flow_squared_length (hq t ht)
      (hf.self_of_nhds t ht) (hregular.self_of_nhds t ht).ne'
      (htime.mono fun y hy ↦ hy t ht) v (htan t ht)
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  exact div_nonneg (mul_nonneg (by norm_num)
    (hhess t (interior_subset ht) _ (htan t (interior_subset ht))))
    (hregular.self_of_nhds t (interior_subset ht)).le



theorem exists_local_normalizedGradient_flow_with_nondecreasing_metric
    (D : LeviCivitaData g) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hregular : ∀ y ∈ U, 0 < g.inner y (D.gradient f y) (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : EuclideanSpace ℝ (Fin n),
      mvfderiv (𝓡 n) f y v = 0 → 0 ≤ D.hessian f y v v)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    ∃ (V : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
      (Φ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ Φ (Ioo (-δ) δ ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ U ∧
        HasDerivAt (fun s => Φ (s, y)) (D.normalizedGradient f (Φ (t, y))) t) ∧
      ∀ y ∈ V, ∀ t ∈ Ico 0 δ,
        f (Φ (t, y)) = f y + t ∧
        ∀ v : EuclideanSpace ℝ (Fin n), mvfderiv (𝓡 n) f y v = 0 →
          g.inner y v v ≤ g.inner (Φ (t, y))
            (fderiv ℝ (fun z => Φ (t, z)) y v)
            (fderiv ℝ (fun z => Φ (t, z)) y v) := by
  obtain ⟨V, δ, q, hV, hxV, hVU, hδ, hq, hinit, hflow⟩ :=
    exists_smooth_normalizedNegGradient_flow D hU hf
      (fun y hy => (hregular y hy).ne') hx
  let Φ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => q (-p.1, p.2)
  have hneg (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : -t ∈ Ioo (-δ) δ := by
    constructor <;> linarith [ht.1, ht.2]
  have hΦ : ContDiffOn ℝ ∞ Φ (Ioo (-δ) δ ×ˢ V) :=
    hq.comp (contDiff_fst.neg.prodMk contDiff_snd).contDiffOn
      (fun p hp => ⟨hneg p.1 hp.1, hp.2⟩)
  have hΦ0 (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) : Φ (0, y) = y := by
    simpa only [Φ, neg_zero] using hinit y hy
  have hΦflow (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      Φ (t, y) ∈ U ∧ HasDerivAt (fun s => Φ (s, y))
        (D.normalizedGradient f (Φ (t, y))) t := by
    refine ⟨(hflow y hy (-t) (hneg t ht)).1, ?_⟩
    have hd := (hflow y hy (-t) (hneg t ht)).2.scomp t ((hasDerivAt_id t).neg)
    simpa only [Φ, Function.comp_def, normalizedGradient, normalizedNegGradient,
      neg_smul, one_smul, neg_neg] using hd
  refine ⟨V, δ, Φ, hV, hxV, hVU, hδ, hΦ, hΦ0, hΦflow, ?_⟩
  intro y hy t ht
  have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
  have hqs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : ContDiffAt ℝ ∞ Φ (s, y) :=
    hΦ.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hsub hs, hy⟩)
  have hfs : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc (0 : ℝ) t,
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (Φ (s, z)) := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact contMDiffAt_iff_contDiffAt.mpr
      (hf.contDiffAt (hU.mem_nhds (hΦflow z hz s (hsub hs)).1))
  have hrs : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc (0 : ℝ) t,
      0 < g.inner (Φ (s, z)) (D.gradient f (Φ (s, z)))
        (D.gradient f (Φ (s, z))) := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact hregular _ (hΦflow z hz s (hsub hs)).1
  have hts : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivAt (fun r => Φ (r, z)) (D.normalizedGradient f (Φ (s, z))) s := by
    filter_upwards [hV.mem_nhds hy] with z hz s hs
    exact (hΦflow z hz s (hsub hs)).2
  constructor
  · have he := comp_normalizedGradient_eq_add D hfs.self_of_nhds
      (fun s hs => (hrs.self_of_nhds s hs).ne') hts.self_of_nhds t ⟨ht.1, le_rfl⟩
    simpa only [hΦ0 y hy, sub_zero] using he
  · intro v hv
    have he : (fun z => Φ (0, z)) =ᶠ[𝓝 y] id := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact hΦ0 z hz
    have hzero : fderiv ℝ (fun z => Φ (0, z)) y v = v := by
      rw [he.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]
    have hm := D.normalizedGradient_flow_squared_length_monotone hqs hfs hrs hts v
      (by rw [hzero, hΦ0 y hy]; exact hv)
      (fun s hs w hw => hhess _ (hΦflow y hy s (hsub hs)).1 w hw)
    have hb := hm ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
    dsimp only at hb
    rw [hzero, hΦ0 y hy] at hb
    exact hb

end PoincareConjecture.LeviCivitaData
