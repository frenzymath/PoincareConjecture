import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.End
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.PathDisplacement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

noncomputable def height (C : M27TwistedSphereLineFlowCertificate K) (x : M) : ℝ :=
  |(C.cover_surjective x).choose.2|

@[simp] theorem height_cover (C : M27TwistedSphereLineFlowCertificate K)
    (p : UnitTwoSphere × ℝ) : C.height (C.cover p) = |p.2| := by
  unfold height
  rcases (C.cover_fibers _ p).mp (C.cover_surjective (C.cover p)).choose_spec with h | h
  · exact congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) h.symm
  · simpa only [m27TwistedProductInvolution, abs_neg] using
      congrArg (fun q : UnitTwoSphere × ℝ => |q.2|) h.symm

theorem height_nonneg (C : M27TwistedSphereLineFlowCertificate K) (x : M) :
    0 ≤ C.height x := abs_nonneg _

theorem mem_slabCore_iff (C : M27TwistedSphereLineFlowCertificate K) (r : ℝ) (x : M) :
    x ∈ C.slabCore r ↔ C.height x ≤ r := by
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  rw [C.cover_mem_slabCore_iff, C.height_cover]

private theorem contMDiff_of_comp_cover (C : M27TwistedSphereLineFlowCertificate K)
    {f : M → ℝ} (hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (f ∘ C.cover)) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f := by
  intro x
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  let h := C.cover_local_diffeomorph p
  have hh := hf.contMDiffAt.comp (C.cover p) h.localInverse_contMDiffAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [h.localInverse_eventuallyEq_right] with y hy
  exact congrArg f hy.symm

private theorem regularized_abs_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun s : ℝ => Real.sqrt (s ^ 2 + δ)) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt (fun s => by positivity)

private theorem regularized_abs_derivative {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + δ))
      (s / Real.sqrt (s ^ 2 + δ)) s := by
  convert (((hasDerivAt_id s).pow 2).add_const δ).sqrt
    (by positivity : s ^ 2 + δ ≠ 0) using 1 <;> dsimp
  ring

private theorem regularized_abs_derivative_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    |s / Real.sqrt (s ^ 2 + δ)| ≤ 1 := by
  have hs : 0 < Real.sqrt (s ^ 2 + δ) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact (Real.sqrt_sq_eq_abs s) ▸ Real.sqrt_le_sqrt (le_add_of_nonneg_right hδ.le)

private theorem regularized_height_smooth (C : M27TwistedSphereLineFlowCertificate K)
    {δ : ℝ} (hδ : 0 < δ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => Real.sqrt (C.height x ^ 2 + δ)) := by
  apply C.contMDiff_of_comp_cover
  simpa only [Function.comp_def, C.height_cover, sq_abs] using
    (contMDiff_iff_contDiff.mpr (regularized_abs_smooth hδ)).comp
      (contMDiff_snd (I := 𝓡 2) (J := 𝓘(ℝ, ℝ)))

private theorem regularized_height_mvfderiv_cover
    (C : M27TwistedSphereLineFlowCertificate K) {δ : ℝ} (hδ : 0 < δ)
    (p : UnitTwoSphere × ℝ) (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    mvfderiv (𝓡 3) (fun x => Real.sqrt (C.height x ^ 2 + δ)) (C.cover p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover p v) =
      (p.2 / Real.sqrt (p.2 ^ 2 + δ)) * v.2 := by
  let f : M → ℝ := fun x => Real.sqrt (C.height x ^ 2 + δ)
  have heq : f ∘ C.cover =
      (fun s : ℝ => Real.sqrt (s ^ 2 + δ)) ∘ Prod.snd := by
    ext q
    simp [f]
  have hf := C.regularized_height_smooth hδ
  have hc := mvfderiv_comp p (hf.mdifferentiable (by simp) (C.cover p))
    (C.cover_local_diffeomorph.contMDiff.mdifferentiable (by simp) p)
  have hh := congrArg (fun D => D v) hc
  change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (f ∘ C.cover) p v = _ at hh
  rw [heq] at hh
  simp only [ContinuousLinearMap.comp_apply] at hh
  rw [← hh, mvfderiv_comp p
    ((contMDiff_iff_contDiff.mpr (regularized_abs_smooth hδ)).mdifferentiable (by simp) p.2)
    ((contMDiff_snd (n := ∞)).mdifferentiable (by simp) p)]
  simp only [mvfderiv, mfderiv_snd, mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply]
  rw [(regularized_abs_derivative hδ p.2).hasFDerivAt.fderiv]
  change v.2 * (p.2 / Real.sqrt (p.2 ^ 2 + δ)) = _
  exact mul_comm _ _

private theorem line_tangent_le (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    |v.2| ≤ (K.flow.metric t).tangentNorm (C.cover p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover p v) := by
  have hn : 0 ≤ (C.sphere.metric t).inner p.1 v.1 v.1 := by
    by_cases hv : v.1 = 0
    · simp [hv]
    · exact ((C.sphere.metric t).pos p.1 v.1 hv).le
  change |v.2| ≤ Real.sqrt _
  rw [C.metric_transport t ht]
  dsimp only [M27RoundSphereFamily.productInner]
  rw [← Real.sqrt_sq_eq_abs v.2]
  apply Real.sqrt_le_sqrt
  nlinarith

private theorem regularized_height_derivative_bound
    (C : M27TwistedSphereLineFlowCertificate K) {t δ : ℝ} (ht : t ≤ 0) (hδ : 0 < δ)
    (x : M) (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (fun y => Real.sqrt (C.height y ^ 2 + δ)) x v| ≤
      (K.flow.metric t).tangentNorm x v := by
  obtain ⟨p, rfl⟩ := C.cover_surjective x
  obtain ⟨w, rfl⟩ := (C.cover_local_diffeomorph.mfderivToContinuousLinearEquiv
    (by simp) p).surjective v
  change |mvfderiv (𝓡 3) (fun y => Real.sqrt (C.height y ^ 2 + δ)) (C.cover p)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover p w)| ≤ _
  rw [C.regularized_height_mvfderiv_cover hδ, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (regularized_abs_derivative_le hδ p.2)).trans
    (C.line_tangent_le ht p w)

theorem edist_height_le (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x y : M) :
    EDist.edist (C.height x) (C.height y) ≤ (K.flow.metric t).edist x y := by
  have hb (δ : ℝ) (hδ : 0 < δ) :
      EDist.edist (Real.sqrt (C.height x ^ 2 + δ))
        (Real.sqrt (C.height y ^ 2 + δ)) ≤ (K.flow.metric t).edist x y := by
    simpa using (K.flow.metric t).edist_le_mul_edist_of_derivative_bound
      ((C.regularized_height_smooth hδ).of_le (by simp)) (K := 1) (by norm_num)
      (fun z v => by simpa using C.regularized_height_derivative_bound ht hδ z v) x y
  have hc : Continuous (fun δ : ℝ =>
      EDist.edist (Real.sqrt (C.height x ^ 2 + δ)) (Real.sqrt (C.height y ^ 2 + δ))) :=
    (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).edist
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id))
  have hlim := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h := le_of_tendsto hlim (eventually_nhdsWithin_of_forall (fun δ hδ => hb δ hδ))
  simpa only [add_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (C.height_nonneg x),
    abs_of_nonneg (C.height_nonneg y)] using h

theorem abs_height_sub_le_toReal_edist (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (x y : M) :
    |C.height x - C.height y| ≤ ((K.flow.metric t).edist x y).toReal := by
  have h := ENNReal.toReal_mono ((K.flow.metric t).edist_ne_top x y)
    (C.edist_height_le ht x y)
  simpa only [edist_dist, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)] using h

theorem edist_le_mem_slabCore (C : M27TwistedSphereLineFlowCertificate K)
    {t r R : ℝ} (ht : t ≤ 0) (hR : 0 ≤ R) {x y : M}
    (hx : x ∈ C.slabCore r) (hy : (K.flow.metric t).edist x y ≤ ENNReal.ofReal R) :
    y ∈ C.slabCore (r + R) := by
  rw [C.mem_slabCore_iff] at hx ⊢
  have hdist : ((K.flow.metric t).edist x y).toReal ≤ R := by
    simpa only [ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  have hh := C.abs_height_sub_le_toReal_edist ht x y
  linarith [neg_le_abs (C.height x - C.height y)]

private theorem edist_cover_line_le_of_le (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere) {a b : ℝ} (hab : a ≤ b) :
    (K.flow.metric t).edist (C.cover (p, a)) (C.cover (p, b)) ≤ ENNReal.ofReal (b - a) := by
  let γ : ℝ → M := fun s => C.cover (p, s)
  have hι : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
    contMDiff_const.prodMk contMDiff_id
  have hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ :=
    C.cover_local_diffeomorph.contMDiff.comp hι
  have hspeed (s : ℝ) :
      (K.flow.metric t).tangentNorm (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) = 1 := by
    change Real.sqrt ((K.flow.metric t).inner _ _ _) = 1
    have hc := mfderiv_comp s
      (C.cover_local_diffeomorph.contMDiff.mdifferentiable (by simp) (p, s))
      (hι.mdifferentiable (by simp) s)
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s = _ at hc
    rw [hc]
    erw [C.metric_transport t ht]
    rw [mfderiv_prod_right]
    norm_num [M27RoundSphereFamily.productInner]
    change (C.sphere.metric t).inner p 0 0 + (1 : ℝ) * 1 = 1
    simp
  simpa only [one_mul] using
    (K.flow.metric t).edist_le_of_tangentNorm_le hab isOpen_univ (subset_univ _)
      hγ.contMDiffOn zero_le_one (fun s _ => (hspeed s).le)

theorem edist_cover_line_le (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere) (a b : ℝ) :
    (K.flow.metric t).edist (C.cover (p, a)) (C.cover (p, b)) ≤ ENNReal.ofReal |a - b| := by
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using
      C.edist_cover_line_le_of_le ht p hab
  · have hc : (K.flow.metric t).edist (C.cover (p, a)) (C.cover (p, b)) =
        (K.flow.metric t).edist (C.cover (p, b)) (C.cover (p, a)) := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(K.flow.metric t).toRiemannianMetric⟩
      exact Manifold.riemannianEDist_comm
    rw [hc, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact C.edist_cover_line_le_of_le ht p hba

theorem edist_cover_line_eq (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (K.flow.metric t).edist (C.cover (p, a)) (C.cover (p, b)) = ENNReal.ofReal |a - b| := by
  apply le_antisymm (C.edist_cover_line_le ht p a b)
  simpa only [C.height_cover, abs_of_nonneg ha, abs_of_nonneg hb, edist_dist, Real.dist_eq] using
    C.edist_height_le ht (C.cover (p, a)) (C.cover (p, b))

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
