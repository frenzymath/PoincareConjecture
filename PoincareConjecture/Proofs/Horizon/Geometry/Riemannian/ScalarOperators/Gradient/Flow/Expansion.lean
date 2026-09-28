import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Convexity.SmoothFlow








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open Poincare.Geometry.Riemannian.Convexity
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData


noncomputable def normalizedGradient
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f : M → ℝ) (x : M) : TangentSpace (𝓡 n) x :=
  (g.inner x (D.gradient f x) (D.gradient f x))⁻¹ • D.gradient f x


private theorem normalizedGradient_eq_neg_normalizedNegGradient
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    D.normalizedGradient f x = -normalizedNegGradient D f x := by
  simp only [normalizedGradient, normalizedNegGradient, neg_smul, neg_neg]

private theorem inner_connection_normalizedGradient_le
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : l ≤ g.tangentNorm x (D.gradient f x))
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0)
    (hhess : D.hessian f x v v ≤ H * g.inner x v v) :
    g.inner x (D.connection (D.normalizedGradient f) x v) v ≤
      (H / l ^ 2) * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hq : l ^ 2 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    change l ^ 2 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    rw [real_inner_self_eq_norm_sq]
    exact (sq_le_sq₀ hl.le (norm_nonneg _)).mpr hgrad
  have hqpos := (sq_pos_of_pos hl).trans_le hq
  have hfield := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hpair : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hfield.inner_bundle hfield
  have hinv : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => (g.inner y (D.gradient f y) (D.gradient f y))⁻¹) x :=
    (differentiableAt_inv hqpos.ne').mdifferentiableAt.comp x hpair
  unfold normalizedGradient
  rw [inner_connection_smul_gradient_of_tangent D hf hinv v hv]
  calc
    _ = D.hessian f x v v / g.inner x (D.gradient f x) (D.gradient f x) := by ring
    _ ≤ (H * g.inner x v v) / g.inner x (D.gradient f x) (D.gradient f x) :=
      div_le_div_of_nonneg_right hhess hqpos.le
    _ = (H / g.inner x (D.gradient f x) (D.gradient f x)) * g.inner x v v := by ring
    _ ≤ (H / l ^ 2) * g.inner x v v :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hH (sq_pos_of_pos hl) hq)
        (show 0 ≤ inner ℝ v v from real_inner_self_nonneg)

private theorem comp_normalizedGradient_eq_add
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
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
  have hl (t : ℝ) : HasDerivAt (fun s => f (γ a) + (s - a)) 1 t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_add (f (γ a))
  exact eq_of_has_deriv_right_eq
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t _ => (hl t).hasDerivWithinAt)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t _ => (hl t).continuousAt.continuousWithinAt) (by simp)



theorem exists_local_normalizedGradient_flow_with_expansion
    {n : ℕ} {g : PoincareConjecture.RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : PoincareConjecture.LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : EuclideanSpace ℝ (Fin n),
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
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
          g.inner (Φ (t, y)) (fderiv ℝ (fun z => Φ (t, z)) y v)
            (fderiv ℝ (fun z => Φ (t, z)) y v) ≤
          g.inner y v v * Real.exp (2 * (H / l ^ 2) * t) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hregular (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
      0 < g.inner y (D.gradient f y) (D.gradient f y) := by
    change 0 < inner ℝ (D.gradient f y) (D.gradient f y)
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (hl.trans_le (hgrad y hy))
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
    simpa only [Φ, Function.comp_def, neg_smul, one_smul,
      normalizedGradient_eq_neg_normalizedNegGradient] using hd
  have hlevel (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (t : ℝ) (ht : t ∈ Ico 0 δ) : f (Φ (t, y)) = f y + t := by
    have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) δ := fun s hs =>
      ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
    have he := comp_normalizedGradient_eq_add D
      (fun s hs => contMDiffAt_iff_contDiffAt.mpr
        (hf.contDiffAt (hU.mem_nhds (hΦflow y hy s (hsub hs)).1)))
      (fun s hs => (hregular _ (hΦflow y hy s (hsub hs)).1).ne')
      (fun s hs => (hΦflow y hy s (hsub hs)).2) t ⟨ht.1, le_rfl⟩
    simpa only [hΦ0 y hy, sub_zero] using he
  refine ⟨V, δ, Φ, hV, hxV, hVU, hδ, hΦ, hΦ0, hΦflow, ?_⟩
  intro y hy t ht
  refine ⟨hlevel y hy t ht, ?_⟩
  intro v hv
  have hsub : Icc (0 : ℝ) t ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], hs.2.trans_lt ht.2⟩
  have hpossub : Icc (0 : ℝ) t ⊆ Ico 0 δ := fun s hs =>
    ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hqs (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : ContDiffAt ℝ ∞ Φ (s, y) :=
    hΦ.contDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hsub hs, hy⟩)
  let w := fun s => fderiv ℝ (fun z => Φ (s, z)) y v
  have htan (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      mvfderiv (𝓡 n) f (Φ (s, y)) (w s) = 0 := by
    have he : (fun z => f (Φ (s, z))) =ᶠ[𝓝 y] fun z => f z + s := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact hlevel z hz s (hpossub hs)
    have hqd : DifferentiableAt ℝ (fun z => Φ (s, z)) y :=
      ((hqs s hs).differentiableAt (by simp)).comp y
        (differentiableAt_const s |>.prodMk differentiableAt_id)
    have hfd := (hf.contDiffAt (hU.mem_nhds (hΦflow y hy s (hsub hs)).1)).differentiableAt
      (by simp)
    have hfy := (hf.contDiffAt (hU.mem_nhds (hVU hy))).differentiableAt (by simp)
    have hleft := hfd.hasFDerivAt.comp y hqd.hasFDerivAt
    have hright := hfy.hasFDerivAt.add_const s
    have heq := congrArg (fun A => A v) (hleft.unique (hright.congr_of_eventuallyEq he))
    have heq' : mvfderiv (𝓡 n) f (Φ (s, y)) (w s) = mvfderiv (𝓡 n) f y v := by
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      convert! heq using 1
    exact heq'.trans hv
  let L := fun s => g.inner (Φ (s, y)) (w s) (w s)
  let L' := fun s => 2 * g.inner (Φ (s, y))
    (D.connection (D.normalizedGradient f) (Φ (s, y)) (w s)) (w s)
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : HasDerivAt L (L' s) s := by
    have hfpoint : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (Φ (s, y)) :=
      contMDiffAt_iff_contDiffAt.mpr
        (hf.contDiffAt (hU.mem_nhds (hΦflow y hy s (hsub hs)).1))
    have hregpoint := (hregular _ (hΦflow y hy s (hsub hs)).1).ne'
    have hfield : DifferentiableAt ℝ (D.normalizedGradient f) (Φ (s, y)) := by
      have heq : D.normalizedGradient f = fun z => -normalizedNegGradient D f z := by
        funext z
        exact normalizedGradient_eq_neg_normalizedNegGradient D f z
      rw [heq]
      exact (differentiableAt_normalizedNegGradient D hfpoint hregpoint).neg
    apply hasDerivAt_flow_squared_length D (hqs s hs) hfield
    filter_upwards [hV.mem_nhds hy] with z hz
    exact (hΦflow z hz s (hsub hs)).2
  have hbound (s : ℝ) (hs : s ∈ Ico (0 : ℝ) t) :
      L' s ≤ -2 * (-(H / l ^ 2)) * L s := by
    have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1, hs.2.le⟩
    have hloc := (hΦflow y hy s (hsub hs')).1
    have hh := inner_connection_normalizedGradient_le D
      (contMDiffAt_iff_contDiffAt.mpr (hf.contDiffAt (hU.mem_nhds hloc)))
      hl hH (hgrad _ hloc) (w s) (htan s hs') (hhess _ hloc _ (htan s hs'))
    dsimp only [L, L']
    linarith
  have hlength := squared_length_le_exp_of_derivative_bound
    (q := L) (q' := L') (c := -(H / l ^ 2))
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => hd s ⟨hs.1, hs.2.le⟩) hbound t ⟨ht.1, le_rfl⟩
  have he : (fun z => Φ (0, z)) =ᶠ[𝓝 y] id := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact hΦ0 z hz
  have hzero : w 0 = v := by
    dsimp only [w]
    rw [he.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply]
  dsimp only [L] at hlength
  rw [hzero, hΦ0 y hy] at hlength
  simpa only [w, sub_zero, mul_neg, neg_mul, neg_neg] using hlength

end PoincareConjecture.LeviCivitaData
