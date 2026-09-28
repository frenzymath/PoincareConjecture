import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.TransitionCompactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Distance
import Mathlib.Geometry.Manifold.LocalDiffeomorph










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter PoincareConjecture Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.AncientVolume.ScalarRatio

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup


theorem pullbackCoefficients_inverse_chart_transition
    (g : RiemannianMetric n M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {a : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (ha : ContMDiffAt (𝓡 n) (𝓡 n) ∞ a x) (hx : a x ∈ Φ.target)
    (u v : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients Φ (Φ.symm (a x))
        (fderiv ℝ (Φ.symm ∘ a) x u) (fderiv ℝ (Φ.symm ∘ a) x v) =
      g.pullbackCoefficients a x u v := by
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := Φ.symm ∘ a
  have hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x :=
    (Φ.symm.contMDiffOn.contMDiffAt (Φ.open_target.mem_nhds hx)).comp x ha
  have hΦ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ Φ (f x) :=
    Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds (Φ.map_target hx))
  have heq : Φ ∘ f =ᶠ[𝓝 x] a := by
    filter_upwards [ha.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hx)]
      with y hy
    exact Φ.right_inv hy
  calc
    _ = g.pullbackCoefficients (Φ ∘ f) x u v := by
      change g.inner (Φ (f x))
        (mfderiv (𝓡 n) (𝓡 n) Φ (f x) (fderiv ℝ f x u))
        (mfderiv (𝓡 n) (𝓡 n) Φ (f x) (fderiv ℝ f x v)) = _
      unfold RiemannianMetric.pullbackCoefficients
      rw [mfderiv_comp x (hΦ.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
      rfl
    _ = _ := by
      change g.inner ((Φ ∘ f) x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ f) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ ∘ f) x v) = _
      rw [heq.mfderiv_eq, heq.self_of_nhds]
      rfl





theorem exists_enclosed_smooth_coordinate_limits
    (g : ℕ → RiemannianMetric n M) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r s R : ℝ} (hrs : r < s) (hsR : s < R)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 R)
    (htarget : ∀ k, (Φ k).target = (g k).ball (q k) R)
    (hradial : ∀ k x, x ∈ Metric.ball 0 R →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    {U : ℕ → Set (EuclideanSpace ℝ (Fin n))} (hU : ∀ i, IsOpen (U i))
    (a : ℕ → ℕ → EuclideanSpace ℝ (Fin n) → M)
    (ha : ∀ i, ∀ᶠ k in atTop,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (a i k) (U i) ∧
      ∀ x ∈ U i, a i k x ∈ (g k).ball (q k) r)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hA : ∀ i, ContDiffOn ℝ ∞ (A i) (U i))
    (hApos : ∀ i x, x ∈ U i → ∀ v, v ≠ 0 → 0 < A i x v v)
    (hAlim : ∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (a i k)))
        (iteratedFDeriv ℝ m (A i)) atTop K)
    (hBlim : ∀ m K, IsCompact K → K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients (Φ k)))
        (iteratedFDeriv ℝ m (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ)) atTop K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        (∀ i, ContDiffOn ℝ ∞ (f i) (U i)) ∧
        (∀ i, MapsTo (f i) (U i) (Metric.closedBall 0 r)) ∧
        (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m ((Φ (σ k)).symm ∘ a i (σ k)))
          (iteratedFDeriv ℝ m (f i)) atTop K) ∧
        (∀ i x, x ∈ U i → ∀ u v,
          inner ℝ (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) = A i x u v) ∧
        (∀ i x, x ∈ U i → Function.Injective (fderiv ℝ (f i) x)) ∧
        ∀ i j x y, x ∈ U i → y ∈ U j →
          (∀ᶠ k in atTop, a i k x = a j k y) → f i x = f j y := by
  let fseq (i k : ℕ) := (Φ k).symm ∘ a i k
  have hinside (k : ℕ) {z : M} (hz : z ∈ (g k).ball (q k) r) :
      z ∈ (Φ k).target := by
    rw [htarget k]
    exact hz.trans_le (ENNReal.ofReal_le_ofReal (hrs.trans hsR).le)
  have hsmall (k : ℕ) {z : M} (hz : z ∈ (g k).ball (q k) r) :
      (Φ k).symm z ∈ Metric.ball 0 r := by
    have he := hradial k ((Φ k).symm z) (hsource k ▸ (Φ k).map_target (hinside k hz))
    have hright : Φ k ((Φ k).symm z) = z := (Φ k).right_inv (hinside k hz)
    rw [hright] at he
    change (g k).edist (q k) z < ENNReal.ofReal r at hz
    rw [he, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)] at hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hAsmooth (i : ℕ) : LocallyEventuallyContDiff (U i)
      (fun k => (g k).pullbackCoefficients (a i k)) := by
    intro K _ hKU
    filter_upwards [ha i] with k hk
    refine ⟨U i, hU i, hKU, fun x hx => ?_⟩
    exact ((g k).contDiffAt_pullbackCoefficients
      (hk.1.contMDiffAt ((hU i).mem_nhds hx))).contDiffWithinAt
  have hBsmooth : LocallyEventuallyContDiff
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s)
      (fun k => (g k).pullbackCoefficients (Φ k)) := by
    intro K _ hKU
    refine Eventually.of_forall fun k => ⟨Metric.ball 0 s, Metric.isOpen_ball, hKU, ?_⟩
    intro x hx
    have hxΦ : x ∈ (Φ k).source :=
      (hsource k).symm ▸ Metric.ball_subset_ball hsR.le hx
    exact ((g k).contDiffAt_pullbackCoefficients
      ((Φ k).contMDiffOn.contMDiffAt ((Φ k).open_source.mem_nhds hxΦ))).contDiffWithinAt
  have hfsmooth (i : ℕ) : LocallyEventuallyContDiff (U i) (fseq i) := by
    intro K _ hKU
    filter_upwards [ha i] with k hk
    refine ⟨U i, hU i, hKU, fun x hx => ?_⟩
    exact (contMDiffAt_iff_contDiffAt.mp
      (((Φ k).symm.contMDiffOn.contMDiffAt
        ((Φ k).open_target.mem_nhds (hinside k (hk.2 x hx)))).comp x
        (hk.1.contMDiffAt ((hU i).mem_nhds hx)))).contDiffWithinAt
  have hcompact (i : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsCompact K)
      (hKU : K ⊆ U i) : ∃ L, IsCompact L ∧ L ⊆ Metric.ball 0 s ∧
      ∀ᶠ k in atTop, MapsTo (fseq i k) K L := by
    refine ⟨Metric.closedBall 0 r, isCompact_closedBall 0 r,
      Metric.closedBall_subset_ball hrs, ?_⟩
    filter_upwards [ha i] with k hk x hx
    exact Metric.ball_subset_closedBall (hsmall k (hk.2 x (hKU hx)))
  have hmetric (i : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) (_ : IsCompact K)
      (hKU : K ⊆ U i) : ∀ᶠ k in atTop, ∀ x ∈ K, ∀ u v,
      (g k).pullbackCoefficients (Φ k) (fseq i k x)
        (fderiv ℝ (fseq i k) x u) (fderiv ℝ (fseq i k) x v) =
      (g k).pullbackCoefficients (a i k) x u v := by
    filter_upwards [ha i] with k hk x hx u v
    exact pullbackCoefficients_inverse_chart_transition (g k) (Φ k)
      (hk.1.contMDiffAt ((hU i).mem_nhds (hKU hx)))
      (hinside k (hk.2 x (hKU hx))) u v
  obtain ⟨σ, hσ, f, hf, _, hlim, hmet⟩ :=
    CoordinateTransition.exists_common_smooth_isometry_limit_of_metric_convergence
      hU (fun _ => Metric.isOpen_ball) hAsmooth (fun _ => hBsmooth) hfsmooth
      hA (fun _ => contDiffOn_const)
      (fun _ k _ _ _ _ => (g k).symm _ _ _)
      (fun _ k _ _ _ _ => (g k).symm _ _ _)
      hApos (fun _ _ _ v hv => real_inner_self_pos.mpr hv) hAlim
      (fun _ => hBlim) hcompact hmetric
  have hpoint (i : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U i) :
      Tendsto (fun k => fseq i (σ k) x) atTop (𝓝 (f i x)) :=
    (CoordinateTransition.locallyUniformly_of_tendsto_zeroJet (hU i) (hlim i 0)).tendsto_at hx
  refine ⟨σ, hσ, f, hf, ?_, hlim, hmet, ?_, ?_⟩
  · intro i x hx
    apply Metric.isClosed_closedBall.mem_of_tendsto (hpoint i hx)
    filter_upwards [hσ.tendsto_atTop.eventually (ha i)] with k hk
    exact Metric.ball_subset_closedBall (hsmall (σ k) (hk.2 x hx))
  · intro i x hx
    apply (injective_iff_map_eq_zero (fderiv ℝ (f i) x)).mpr
    intro v hv
    by_contra hne
    have he := hmet i x hx v v
    rw [hv] at he
    have he' : A i x v v = 0 := by simpa only [map_zero, zero_apply] using he.symm
    exact (hApos i x hx v hne).ne' he'
  · intro i j x y hx hy heq
    apply tendsto_nhds_unique (hpoint i hx)
    apply (hpoint j hy).congr'
    filter_upwards [hσ.tendsto_atTop.eventually heq] with k hk
    change (Φ (σ k)).symm (a j (σ k) y) = (Φ (σ k)).symm (a i (σ k) x)
    rw [hk]




theorem exists_smooth_isometric_immersion_of_compatible_charts
    {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    (h : RiemannianMetric n X)
    (e : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) X ∞)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).target)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (e i).source)
    (hcompat : ∀ i j x y, x ∈ (e i).source → y ∈ (e j).source →
      e i x = e j y → f i x = f j y)
    (hmetric : ∀ i x, x ∈ (e i).source → ∀ u v,
      inner ℝ (fderiv ℝ (f i) x u) (fderiv ℝ (f i) x v) =
        h.pullbackCoefficients (e i) x u v) :
    ∃ F : X → EuclideanSpace ℝ (Fin n),
      ContMDiff (𝓡 n) (𝓡 n) ∞ F ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 n) F x)) ∧
      (∀ x, ∀ u v : TangentSpace (𝓡 n) x,
        inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x u) (mfderiv (𝓡 n) (𝓡 n) F x v) =
          h.inner x u v) ∧
      ∀ i x, x ∈ (e i).source → F (e i x) = f i x := by
  classical
  choose index hindex using hcover
  let F : X → EuclideanSpace ℝ (Fin n) := fun x => f (index x) ((e (index x)).symm x)
  have hchart (i : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ (e i).source) :
      F (e i x) = f i x := by
    apply (hcompat i (index (e i x)) x ((e (index (e i x))).symm (e i x)) hx
      ((e (index (e i x))).map_target (hindex (e i x))) ?_).symm
    exact ((e (index (e i x))).right_inv (hindex (e i x))).symm
  have hlocal (i : ℕ) (x : X) (hx : x ∈ (e i).target) :
      F =ᶠ[𝓝 x] f i ∘ (e i).symm := by
    filter_upwards [(e i).open_target.mem_nhds hx] with y hy
    have hh := hchart i ((e i).symm y) ((e i).map_target hy)
    have hright : e i ((e i).symm y) = y := (e i).right_inv hy
    simpa only [hright, Function.comp_apply] using hh
  have hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F := by
    intro x
    let i := index x
    have hi := hindex x
    have hfi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (f i) ((e i).symm x) :=
      ((hf i).contDiffAt ((e i).open_source.mem_nhds ((e i).map_target hi))).contMDiffAt
    exact (hfi.comp x ((e i).symm.contMDiffOn.contMDiffAt
      ((e i).open_target.mem_nhds hi))).congr_of_eventuallyEq (hlocal i x hi)
  have hmetric' (i : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (e i).source) :
      ∀ u v : TangentSpace (𝓡 n) (e i z),
        inner ℝ (mfderiv (𝓡 n) (𝓡 n) F (e i z) u)
          (mfderiv (𝓡 n) (𝓡 n) F (e i z) v) = h.inner (e i z) u v := by
    have heq : F ∘ e i =ᶠ[𝓝 z] f i := by
      filter_upwards [(e i).open_source.mem_nhds hz] with w hw
      exact hchart i w hw
    have hderiv : (mfderiv (𝓡 n) (𝓡 n) F (e i z)).comp
        (mfderiv (𝓡 n) (𝓡 n) (e i) z) = fderiv ℝ (f i) z := by
      rw [← mfderiv_comp z ((hF (e i z)).mdifferentiableAt (by simp))
        (((e i).contMDiffOn.contMDiffAt ((e i).open_source.mem_nhds hz)).mdifferentiableAt
          (by simp)), heq.mfderiv_eq, mfderiv_eq_fderiv]
    have hsurj := ((e i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hz).mfderivToContinuousLinearEquiv
      (by simp) |>.surjective
    intro u v
    obtain ⟨u', rfl⟩ := hsurj u
    obtain ⟨v', rfl⟩ := hsurj v
    have hu := congrArg (fun L => L u') hderiv
    have hv := congrArg (fun L => L v') hderiv
    simp only [ContinuousLinearMap.comp_apply] at hu hv
    change inner ℝ
      (mfderiv (𝓡 n) (𝓡 n) F (e i z) (mfderiv (𝓡 n) (𝓡 n) (e i) z u'))
      (mfderiv (𝓡 n) (𝓡 n) F (e i z) (mfderiv (𝓡 n) (𝓡 n) (e i) z v')) = _
    rw [hu, hv]
    exact hmetric i z hz u' v'
  have hglobal (x : X) : ∀ u v : TangentSpace (𝓡 n) x,
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) F x u) (mfderiv (𝓡 n) (𝓡 n) F x v) =
        h.inner x u v := by
    let i := index x
    have hi := hindex x
    have hright : e i ((e i).symm x) = x := (e i).right_inv hi
    rw [← hright]
    exact hmetric' i ((e i).symm x) ((e i).map_target hi)
  refine ⟨F, hF, ?_, hglobal, hchart⟩
  intro x
  apply (injective_iff_map_eq_zero (mfderiv (𝓡 n) (𝓡 n) F x)).mpr
  intro v hv
  by_contra hne
  have he := hglobal x v v
  rw [hv] at he
  change (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) 0 0 = _ at he
  simp only [map_zero] at he
  exact (h.pos x v hne).ne' he.symm




theorem lower_distance_of_enclosed_euclidean_limit
    (g : ℕ → RiemannianMetric n M)
    (Φ : ℕ → EuclideanSpace ℝ (Fin n) → M)
    {r : ℝ} (hΦ : ∀ k, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k) (Metric.ball 0 r))
    (hcoeff : TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
      (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ) atTop (Metric.closedBall 0 r))
    {xseq yseq : ℕ → EuclideanSpace ℝ (Fin n)}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : Tendsto xseq atTop (𝓝 x)) (hy : Tendsto yseq atTop (𝓝 y))
    (hinside : ∀ᶠ k in atTop, xseq k ∈ Metric.ball 0 r ∧ yseq k ∈ Metric.ball 0 r)
    {dseq : ℕ → ℝ} {d : ℝ} (hd : Tendsto dseq atTop (𝓝 d))
    (hlower : ∀ᶠ k in atTop,
      dseq k ≤ ((g k).edist (Φ k (xseq k)) (Φ k (yseq k))).toReal) :
    d ≤ dist x y := by
  let : NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  have hEval (v w : EuclideanSpace ℝ (Fin n)) : B₀ v w = inner ℝ v w := rfl
  have hbound (ε : ℝ) (hε : 0 < ε) : d ≤ Real.sqrt (1 + ε) * dist x y := by
    have hupper : ∀ᶠ k in atTop, ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ∀ v, (g k).pullbackCoefficients (Φ k) z v v ≤ (1 + ε) * ‖v‖ ^ 2 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hcoeff ε hε] with k hk z hz v
      have hnorm : ‖(g k).pullbackCoefficients (Φ k) z - B₀‖ ≤ ε := by
        simpa only [B₀, dist_eq_norm, norm_sub_rev] using
          (hk z (Metric.ball_subset_closedBall hz)).le
      have herr : |(g k).pullbackCoefficients (Φ k) z v v - inner ℝ v v| ≤
          ε * ‖v‖ ^ 2 := by
        calc
          _ ≤ ‖(g k).pullbackCoefficients (Φ k) z - B₀‖ * ‖v‖ * ‖v‖ := by
            simpa only [sub_apply, hEval, Real.norm_eq_abs] using
              ((g k).pullbackCoefficients (Φ k) z - B₀).le_opNorm₂ v v
          _ ≤ ε * ‖v‖ ^ 2 := by
            simpa only [pow_two, mul_assoc] using
              mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg v) (norm_nonneg v))
      have hsq : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      linarith [(abs_le.mp herr).2]
    apply le_of_tendsto_of_tendsto hd (tendsto_const_nhds.mul (hx.dist hy))
    filter_upwards [hinside, hlower, hupper] with k hkin hklo hkup
    exact hklo.trans ((g k).toReal_edist_le_of_pullback_upper Metric.isOpen_ball
      (convex_ball 0 r) (hΦ k) (by positivity) hkup hkin.1 hkin.2)
  have hlim : Tendsto (fun ε : ℝ => Real.sqrt (1 + ε) * dist x y)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist x y)) := by
    have hcont : ContinuousAt (fun ε : ℝ => Real.sqrt (1 + ε) * dist x y) 0 := by
      fun_prop
    simpa only [nhdsWithin, add_zero, Real.sqrt_one, one_mul] using
      hcont.tendsto.mono_left (show 𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0) ≤ 𝓝 0 from inf_le_left)
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)

end Poincare.AncientVolume.ScalarRatio
