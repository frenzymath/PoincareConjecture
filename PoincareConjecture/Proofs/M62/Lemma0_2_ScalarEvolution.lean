import PoincareConjecture.Proofs.M62.Lemma0_2_NormalizedFields
import PoincareConjecture.Proofs.M62.Cor0_3_RegularizedGradient
import PoincareConjecture.Proofs.M62.Sec19_1_MovingCommutation










set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

set_option maxHeartbeats 2000000 in



theorem curvature_squared_arcSecond_eq [T2Space M]
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x =
      2 * (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (fun y =>
          m62SpatialDerivative F c t (m62CurvatureVector F c t) y) x)
        (m62CurvatureVector F c t x) +
      2 * (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (m62CurvatureVector F c t) x)
        (m62SpatialDerivative F c t (m62CurvatureVector F c t) x) := by
  let Ω : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo a b
  let D := F.connection t
  let H : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62CurvatureVector F c t y
  let B : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62SpatialDerivative F c t (m62CurvatureVector F c t) y
  let C : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62SpatialDerivative F c t B y
  have hvpos : 0 < curveSpeed F c t x :=
    speed_pos F c hc (Ioo_subset_Icc_self ht) x
  have hDxH : rampHorizontalCovariantDerivative D (fun y => c y t) H x =
      curveSpeed F c t x • B x := by
    dsimp only [B, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hArc (y : ℝ) :
      m62ArcDerivative F c t (m62CurvatureSquared F c t) y =
        2 * (F.metric t).inner (c y t) (B y) (H y) := by
    have hv : curveSpeed F c t y ≠ 0 :=
      (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne'
    have hq := hasDerivAt_curvatureSquared_parameter F c hc ht y
    have hDx : rampHorizontalCovariantDerivative D (fun z => c z t) H y =
        curveSpeed F c t y • B y := by
      dsimp only [B, m62SpatialDerivative]
      rw [smul_smul, mul_inv_cancel₀ hv, one_smul]
    rw [m62ArcDerivative, hq.deriv]
    rw [hDx]
    simp only [map_smul, smul_apply, smul_eq_mul, H]
    field_simp
  have hHjoint := curvature_joint_contMDiff F c hc
  have hBjoint := spatialDerivative_joint_contMDiff F c hc
      (fun z => m62CurvatureVector F c z.2 z.1) hHjoint
  have hmem : (x, t) ∈ Ω := ⟨mem_univ _, ht⟩
  have hopen : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun y => c y t) x :=
    (((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
  have hH : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, H y⟩ : TangentBundle (𝓡 n) M)) x := by
    have h := (((hHjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
    simpa only [Function.comp_def, H] using h
  have hB : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, B y⟩ : TangentBundle (𝓡 n) M)) x := by
    have h := (((hBjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
    simpa only [Function.comp_def, B] using h
  have hpair := hasDerivAt_metric_pairing D hγ hB hH
  have hDxB : rampHorizontalCovariantDerivative D (fun y => c y t) B x =
      curveSpeed F c t x • C x := by
    dsimp only [C, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hArcDeriv :
      HasDerivAt (fun y => m62ArcDerivative F c t
        (m62CurvatureSquared F c t) y)
      (2 * ((F.metric t).inner (c x t)
          (rampHorizontalCovariantDerivative D (fun y => c y t) B x) (H x) +
        (F.metric t).inner (c x t) (B x)
          (rampHorizontalCovariantDerivative D (fun y => c y t) H x))) x := by
    rw [show (fun y => m62ArcDerivative F c t
        (m62CurvatureSquared F c t) y) =
      (fun y => 2 * (F.metric t).inner (c y t) (B y) (H y)) from funext hArc]
    exact hpair.const_mul 2
  rw [m62ArcSecondDerivative, m62ArcDerivative, hArcDeriv.deriv,
    hDxB, hDxH]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp
  ring



theorem spatialDerivative_norm_split
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    (F.metric t).inner (c x t)
      (m62SpatialDerivative F c t (m62CurvatureVector F c t) x)
      (m62SpatialDerivative F c t (m62CurvatureVector F c t) x) =
      (F.metric t).inner (c x t) (m62SpatialNormalDerivative F c t x)
        (m62SpatialNormalDerivative F c t x) +
      m62CurvatureSquared F c t x ^ 2 := by
  let D := F.connection t
  let S : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => spatialUnitTangent F c t y
  let H : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62CurvatureVector F c t y
  let B : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62SpatialDerivative F c t (m62CurvatureVector F c t) y
  have hvpos : 0 < curveSpeed F c t x :=
    speed_pos F c hc (Ioo_subset_Icc_self ht) x
  have hDxH : rampHorizontalCovariantDerivative D (fun y => c y t) H x =
      curveSpeed F c t x • B x := by
    dsimp only [B, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hDxS : rampHorizontalCovariantDerivative D (fun y => c y t) S x =
      curveSpeed F c t x • H x := by
    dsimp only [H, m62CurvatureVector, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hmem : (x, t) ∈ (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    ⟨mem_univ _, ht⟩
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hγ := (((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
    (by simp)).comp x hspace)
  have hHjoint := curvature_joint_contMDiff F c hc
  have hH := ((((hHjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
    (by simp)).comp x hspace))
  have hS := (unitTangent_contMDiff F c hc (Ioo_subset_Icc_self ht) x).mdifferentiableAt
    (by simp)
  have hγ' : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun y => c y t) x := by simpa only [Function.comp_def] using hγ
  have hH' : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, H y⟩ : TangentBundle (𝓡 n) M)) x := by
    simpa only [Function.comp_def, H] using hH
  have hS' : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, S y⟩ : TangentBundle (𝓡 n) M)) x := by
    simpa only [Function.comp_def, S] using hS
  have hpair := hasDerivAt_metric_pairing D hγ' hH' hS'
  have hzero : (fun y => (F.metric t).inner (c y t) (H y) (S y)) =
      (fun _ : ℝ => 0) := by
    funext y
    exact curvature_unitTangent_inner_zero F c hc (Ioo_subset_Icc_self ht) y
  change HasDerivAt (fun y => (F.metric t).inner (c y t) (H y) (S y)) _ x at hpair
  rw [hzero] at hpair
  have hBS0 := hpair.unique (hasDerivAt_const x (0 : ℝ))
  rw [hDxH, hDxS] at hBS0
  simp only [map_smul, smul_apply, smul_eq_mul] at hBS0
  have hHH0 : (F.metric t).inner (c x t) (H x) (H x) =
      m62CurvatureSquared F c t x := rfl
  rw [hHH0] at hBS0
  have hfactor : curveSpeed F c t x *
      ((F.metric t).inner (c x t) (B x) (S x) +
        m62CurvatureSquared F c t x) = 0 := by
    nlinarith [hBS0]
  have hBS : (F.metric t).inner (c x t) (B x) (S x) =
      -m62CurvatureSquared F c t x := by
    have hsum := (mul_eq_zero.mp hfactor).resolve_left hvpos.ne'
    linarith
  change (F.metric t).inner (c x t) (B x) (B x) =
    (F.metric t).inner (c x t)
      (B x - (F.metric t).inner (c x t) (B x) (S x) • S x)
      (B x - (F.metric t).inner (c x t) (B x) (S x) • S x) +
      m62CurvatureSquared F c t x ^ 2
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
  rw [(F.metric t).symm (c x t) (S x) (B x), hBS,
    unitTangent_inner_self F c hc (Ioo_subset_Icc_self ht) x]
  ring

set_option maxHeartbeats 5000000 in



theorem curvature_squared_time_pair [T2Space M]
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Set.Ioo a b) (x : ℝ) :
    (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative (F.connection t) (fun r => c x r)
        (fun r => m62CurvatureVector F c r x) t)
      (m62CurvatureVector F c t x) =
      (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (fun y =>
          m62SpatialDerivative F c t (m62CurvatureVector F c t) y) x)
        (m62CurvatureVector F c t x) +
      2 * (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
        m62CurvatureSquared F c t x +
      (F.connection t).curvatureTensor (c x t)
        (m62CurvatureVector F c t x) (spatialUnitTangent F c t x)
        (m62CurvatureVector F c t x) (spatialUnitTangent F c t x) -
      2 * (F.connection t).covariantTensorDerivative
        (F.connection t).ricciEvaluation (c x t)
        ![spatialUnitTangent F c t x, spatialUnitTangent F c t x,
          m62CurvatureVector F c t x] +
      (F.connection t).covariantTensorDerivative
        (F.connection t).ricciEvaluation (c x t) ![
          m62CurvatureVector F c t x, spatialUnitTangent F c t x,
          spatialUnitTangent F c t x] := by
  let Ω : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo a b
  let D := F.connection t
  let S : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => spatialUnitTangent F c z.2 z.1
  let H : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m62CurvatureVector F c z.2 z.1
  let B : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m62SpatialDerivative F c z.2
      (fun y => m62CurvatureVector F c z.2 y) z.1
  let C : (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun y => m62SpatialDerivative F c t
      (fun z => m62SpatialDerivative F c t (m62CurvatureVector F c t) z) y
  let A : ℝ × ℝ → ℝ := fun z =>
    m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1
  have hopen : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ Ω := ⟨mem_univ _, ht⟩
  have hspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have htime : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ))
      (fun r : ℝ => (x, r)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hspaceD : DifferentiableAt ℝ (fun y : ℝ => (y, t)) x :=
    differentiableAt_id.prodMk (differentiableAt_const t)
  have htimeD : DifferentiableAt ℝ (fun r : ℝ => (x, r)) t :=
    (differentiableAt_const x).prodMk differentiableAt_id
  have hγspace : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun y : ℝ => c y t) x := by
    exact (((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
  have hγtime : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n)
      (fun r : ℝ => c x r) t := by
    exact (((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime)
  have hSjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, S z⟩ : TangentBundle (𝓡 n) M)) Ω := by
    simpa only [S] using unitTangent_joint_contMDiff F c hc
  have hHjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, H z⟩ : TangentBundle (𝓡 n) M)) Ω := by
    simpa only [H] using curvature_joint_contMDiff F c hc
  have hBjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, B z⟩ : TangentBundle (𝓡 n) M)) Ω := by
    simpa only [B] using spatialDerivative_joint_contMDiff F c hc
      (fun z => m62CurvatureVector F c z.2 z.1) (by
        simpa only [H] using hHjoint)
  have hSspace : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y : ℝ => (⟨c y t, S (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    exact (((hSjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
  have hHspace : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y : ℝ => (⟨c y t, H (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    exact (((hHjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
  have hBspace : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y : ℝ => (⟨c y t, B (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    exact (((hBjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace)
  have hStime : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun r : ℝ => (⟨c x r, S (x, r)⟩ : TangentBundle (𝓡 n) M)) t := by
    exact (((hSjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime)
  have hHtime : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun r : ℝ => (⟨c x r, H (x, r)⟩ : TangentBundle (𝓡 n) M)) t := by
    exact (((hHjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime)
  have hAcont : ContDiffOn ℝ ∞ A Ω := by
    simpa only [A] using normalization_coefficient_contDiffOn F c hc
  have hAxy : ContDiffAt ℝ ∞ A (x, t) :=
    hAcont.contDiffAt (hopen.mem_nhds hmem)
  have hAspaceD : DifferentiableAt ℝ (fun y : ℝ => A (y, t)) x := by
    simpa only [Function.comp_def] using
      (hAxy.differentiableAt (by simp)).comp x hspaceD
  have hAspace : HasDerivAt (fun y : ℝ => A (y, t))
      (deriv (fun y : ℝ => A (y, t)) x) x := hAspaceD.hasDerivAt
  have hAS : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun y : ℝ => (⟨c y t, A (y, t) • S (y, t)⟩ : TangentBundle (𝓡 n) M)) x := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨hγspace, ?_⟩
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (c x t)
    let ycoord : ℝ → EuclideanSpace ℝ (Fin n) := fun y =>
      (e ⟨c y t, S (y, t)⟩).2
    have hycoord : MDifferentiableAt (𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ycoord x := by
      have hscoord := hSspace
      rw [mdifferentiableAt_totalSpace] at hscoord
      simpa only [ycoord] using hscoord.2
    have hnear : ∀ᶠ y in 𝓝 x, c y t ∈ e.baseSet :=
      hγspace.continuousAt (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (c x t)))
    have hcoord := hAspaceD.mdifferentiableAt.smul hycoord
    apply hcoord.congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    change (e ⟨c y t, A (y, t) • S (y, t)⟩).2 =
      A (y, t) • ycoord y
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hy] using
      (e.continuousLinearMapAt ℝ (c y t)).map_smul (A (y, t)) (S (y, t))
  have hspeed := hasDerivAt_speed F c hc ht x
  have hDSgerm : ∀ᶠ r in 𝓝 t,
      rampHorizontalCovariantDerivative (F.connection r) (fun s => c s r)
          (fun s => S (s, r)) x = curveSpeed F c r x • H (x, r) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    have hv := speed_pos F c hc (Ioo_subset_Icc_self hr) x
    dsimp only [S, H, m62CurvatureVector, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hv.ne', one_smul]
  have hA1 : rampHorizontalCovariantDerivative D (fun r => c x r)
      (fun r => rampHorizontalCovariantDerivative (F.connection r)
        (fun s => c s r) (fun s => S (s, r)) x) t =
      (-(A (x, t) * curveSpeed F c t x)) • H (x, t) +
        curveSpeed F c t x •
          rampHorizontalCovariantDerivative D (fun r => c x r)
            (fun r => H (x, r)) t := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun r => c x r)
          (fun r => curveSpeed F c r x • H (x, r)) t :=
        pullback_congr D hDSgerm
      _ = _ := by
        simpa only [A, neg_mul] using pullback_smul D hspeed hHtime
  have hunit (y : ℝ) :
      rampHorizontalCovariantDerivative D (fun r => c y r)
          (fun r => S (y, r)) t = B (y, t) + A (y, t) • S (y, t) := by
    simpa only [D, S, H, B, A] using unitTangent_time_derivative F c hc ht y
  have hA2 : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => rampHorizontalCovariantDerivative D (fun r => c y r)
        (fun r => S (y, r)) t) x =
      rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => B (y, t)) x +
      (deriv (fun y => A (y, t)) x) • S (x, t) +
      A (x, t) • rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => S (y, t)) x := by
    calc
      _ = rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => B (y, t) + A (y, t) • S (y, t)) x :=
        pullback_congr D
          (Y := fun y => rampHorizontalCovariantDerivative D (fun r => c y r)
            (fun r => S (y, r)) t)
          (Z := fun y => B (y, t) + A (y, t) • S (y, t))
          (Filter.Eventually.of_forall hunit)
      _ = rampHorizontalCovariantDerivative D (fun y => c y t)
          (fun y => B (y, t)) x +
          rampHorizontalCovariantDerivative D (fun y => c y t)
            (fun y => A (y, t) • S (y, t)) x :=
        pullback_add D hBspace hAS
      _ = _ := by
        rw [pullback_smul D hAspace hSspace]
        abel
  have hDxS : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => S (y, t)) x = curveSpeed F c t x • H (x, t) := by
    dsimp only [S, H, m62CurvatureVector, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀
      (ne_of_gt (speed_pos F c hc (Ioo_subset_Icc_self ht) x)), one_smul]
  have hHS : (F.metric t).inner (c x t) (H (x, t)) (S (x, t)) = 0 := by
    simpa only [H, S] using curvature_unitTangent_inner_zero F c hc
      (Ioo_subset_Icc_self ht) x
  have hSH : (F.metric t).inner (c x t) (S (x, t)) (H (x, t)) = 0 := by
    rw [(F.metric t).symm (c x t) (S (x, t)) (H (x, t))]
    exact hHS
  have hHH : (F.metric t).inner (c x t) (H (x, t)) (H (x, t)) =
      m62CurvatureSquared F c t x := rfl
  have hA1pair := congrArg (fun V => (F.metric t).inner (c x t) V (H (x, t))) hA1
  have hA2pair := congrArg (fun V => (F.metric t).inner (c x t) V (H (x, t))) hA2
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul] at hA1pair hA2pair
  rw [hHH] at hA1pair
  rw [hSH] at hA2pair
  rw [hDxS] at hA2pair
  simp only [map_smul, smul_apply, smul_eq_mul] at hA2pair
  rw [hHH] at hA2pair
  have hcomm := flow_pullback_curvature_pair F c S hopen
    (fun z hz => by simpa only [interior_Icc] using hz.2) hc.joint_smooth hSjoint hmem
      (H (x, t))
  simp only [map_sub, sub_apply] at hcomm
  have hvpos : 0 < curveSpeed F c t x :=
    speed_pos F c hc (Ioo_subset_Icc_self ht) x
  have hX : curveVelocity (fun s => c s t) x =
      curveSpeed F c t x • S (x, t) := by
    dsimp only [S, spatialUnitTangent]
    change curveVelocity (fun s => c s t) x =
      curveSpeed F c t x •
        (curveSpeed F c t x)⁻¹ • curveVelocity (fun s => c s t) x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
  have hU : curveVelocity (fun r => c x r) t = H (x, t) := by
    simpa only [H] using hc.equation t ht x
  rw [hX, hU] at hcomm
  have hcurvScale : (F.metric t).inner (c x t)
      (D.curvature (c x t) (H (x, t))
        (curveSpeed F c t x • S (x, t)) (S (x, t))) (H (x, t)) =
      curveSpeed F c t x * D.curvatureTensor (c x t) (H (x, t))
        (S (x, t)) (H (x, t)) (S (x, t)) := by
    change D.curvatureTensor (c x t) (H (x, t))
        (curveSpeed F c t x • S (x, t)) (H (x, t)) (S (x, t)) =
      curveSpeed F c t x * D.curvatureTensor (c x t) (H (x, t))
        (S (x, t)) (H (x, t)) (S (x, t))
    obtain ⟨R, hR⟩ := (M04.isSmoothCovariantTensor_riemannEvaluation D).1 (c x t)
    have hscale := R.map_smul_univ
      ![1, curveSpeed F c t x, 1, 1] ![H (x, t), S (x, t), H (x, t), S (x, t)]
    have heq : (fun i : Fin 4 =>
        ![1, curveSpeed F c t x, 1, 1] i •
          ![H (x, t), S (x, t), H (x, t), S (x, t)] i) =
        ![H (x, t), curveSpeed F c t x • S (x, t), H (x, t), S (x, t)] := by
      funext i
      fin_cases i <;> simp
    rw [heq] at hscale
    rw [← hR, ← hR] at hscale
    simpa [LeviCivitaData.riemannEvaluation, Fin.prod_univ_succ] using hscale
  obtain ⟨K, hK⟩ :=
    (M04.isSmoothCovariantTensor_covariantTensorDerivative D
      (M04.isSmoothCovariantTensor_ricciEvaluation D)).1 (c x t)
  have hderScale (W : Fin 3 → TangentSpace (𝓡 n) (c x t))
      (V : Fin 3 → TangentSpace (𝓡 n) (c x t))
      (i : Fin 3) (f : ℝ)
      (hi : W i = f • V i)
      (hj : ∀ j, j ≠ i → W j = V j) :
      D.covariantTensorDerivative D.ricciEvaluation (c x t) W =
        f * D.covariantTensorDerivative D.ricciEvaluation (c x t) V := by
    have hscale := K.map_smul_univ
      (fun j => if j = i then f else 1) V
    have heq : (fun j => (if j = i then f else 1) • V j) = W := by
      funext j
      by_cases hji : j = i
      · subst j
        rw [if_pos (by rfl)]
        exact hi.symm
      · rw [if_neg hji, one_smul, hj j hji]
    rw [heq] at hscale
    rw [← hK, ← hK] at hscale
    have hprod : ∏ j : Fin 3, (if j = i then f else 1) = f := by
      fin_cases i <;> simp
    simpa only [hprod, smul_eq_mul] using hscale
  have hder1 : D.covariantTensorDerivative D.ricciEvaluation (c x t) ![
      curveSpeed F c t x • S (x, t), S (x, t), H (x, t)] =
      curveSpeed F c t x * D.covariantTensorDerivative D.ricciEvaluation
        (c x t) ![S (x, t), S (x, t), H (x, t)] := by
    apply hderScale ![curveSpeed F c t x • S (x, t), S (x, t), H (x, t)]
      ![S (x, t), S (x, t), H (x, t)] 0 (curveSpeed F c t x)
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  have hder2 : D.covariantTensorDerivative D.ricciEvaluation (c x t) ![
      S (x, t), curveSpeed F c t x • S (x, t), H (x, t)] =
      curveSpeed F c t x * D.covariantTensorDerivative D.ricciEvaluation
        (c x t) ![S (x, t), S (x, t), H (x, t)] := by
    apply hderScale ![S (x, t), curveSpeed F c t x • S (x, t), H (x, t)]
      ![S (x, t), S (x, t), H (x, t)] 1 (curveSpeed F c t x)
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  have hder3 : D.covariantTensorDerivative D.ricciEvaluation (c x t) ![
      H (x, t), curveSpeed F c t x • S (x, t), S (x, t)] =
      curveSpeed F c t x * D.covariantTensorDerivative D.ricciEvaluation
        (c x t) ![H (x, t), S (x, t), S (x, t)] := by
    apply hderScale ![H (x, t), curveSpeed F c t x • S (x, t), S (x, t)]
      ![H (x, t), S (x, t), S (x, t)] 1 (curveSpeed F c t x)
    · simp
    · intro j hj
      fin_cases j <;> simp_all
  have hDxB : rampHorizontalCovariantDerivative D (fun y => c y t)
      (fun y => B (y, t)) x = curveSpeed F c t x • C x := by
    dsimp only [B, C, m62SpatialDerivative]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  rw [hDxB] at hA2pair
  simp only [map_smul, smul_apply, smul_eq_mul] at hA2pair
  rw [hcurvScale, hder1, hder2, hder3] at hcomm
  rw [hA1pair, hA2pair] at hcomm
  have hfinal : (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative D (fun r => c x r)
        (fun r => H (x, r)) t) (H (x, t)) =
      (F.metric t).inner (c x t) (C x) (H (x, t)) +
        2 * A (x, t) * m62CurvatureSquared F c t x +
      D.curvatureTensor (c x t) (H (x, t)) (S (x, t))
        (H (x, t)) (S (x, t)) -
      2 * D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![S (x, t), S (x, t), H (x, t)] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![H (x, t), S (x, t), S (x, t)] := by
    apply (mul_left_cancel₀ (ne_of_gt hvpos))
    nlinarith [hcomm]
  simpa only [A, C, D, S, H, add_comm] using hfinal

end PoincareConjecture.M62
