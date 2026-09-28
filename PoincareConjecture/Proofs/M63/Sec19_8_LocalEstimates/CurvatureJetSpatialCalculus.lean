import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SmoothRelabeling
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureVectorEvolution

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63ArcDerivative_metric_pairing
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c)
    (Y Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b))
    (hZ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Z z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    m62ArcDerivative F c t
      (fun y => (F.metric t).inner (c y t) (Y (y, t)) (Z (y, t))) x =
      (F.metric t).inner (c x t)
        (m62SpatialDerivative F c t (fun y => Y (y, t)) x) (Z (x, t)) +
      (F.metric t).inner (c x t) (Y (x, t))
        (m62SpatialDerivative F c t (fun y => Z (y, t)) x) := by
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t) x :=
    ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hs
  have hYs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, Y (y, t)⟩ : TangentBundle (𝓡 n) M)) x :=
    ((hY.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hs
  have hZs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, Z (y, t)⟩ : TangentBundle (𝓡 n) M)) x :=
    ((hZ.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp x hs
  have hpair := hasDerivAt_metric_pairing (F.connection t) hcurve hYs hZs
  rw [m62ArcDerivative, hpair.deriv]
  simp only [m62SpatialDerivative, map_smul, smul_apply, smul_eq_mul, mul_add]

theorem m63CurvatureJetSquared_joint_contDiff [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => m63CurvatureJetSquared F c i z.2 z.1)
      (univ ×ˢ Ioo a b) := by
  have hjet := M63.curvatureJet_joint_contMDiff F c hc i
  exact metric_pairing_contDiffOn F c hc.joint_smooth
    (fun z => m63CurvatureJet F c i z.2 z.1)
    (fun z => m63CurvatureJet F c i z.2 z.1) hjet hjet

theorem m63CurvatureJetSquared_arcSecond_eq [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c i t) x =
      2 * (F.metric t).inner (c x t)
        (m63CurvatureJet F c (i + 2) t x) (m63CurvatureJet F c i t x) +
      2 * m63CurvatureJetSquared F c (i + 1) t x := by
  let Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c i z.2 z.1
  let Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c (i + 1) z.2 z.1
  have hY := M63.curvatureJet_joint_contMDiff F c hc i
  have hZ := M63.curvatureJet_joint_contMDiff F c hc (i + 1)
  let P : ℝ → ℝ := fun y => (F.metric t).inner (c y t) (Z (y, t)) (Y (y, t))
  have hArc (y : ℝ) :
      m62ArcDerivative F c t (m63CurvatureJetSquared F c i t) y = 2 * P y := by
    have h := m63ArcDerivative_metric_pairing F c hc Y Y hY hY ht y
    change m62ArcDerivative F c t (m63CurvatureJetSquared F c i t) y =
      (F.metric t).inner (c y t) (Z (y, t)) (Y (y, t)) +
        (F.metric t).inner (c y t) (Y (y, t)) (Z (y, t)) at h
    rw [(F.metric t).symm (c y t) (Y (y, t)) (Z (y, t))] at h
    dsimp only [P]
    linarith
  have hP : ContDiff ℝ ∞ P :=
    (metric_pairing_contDiffOn F c hc.joint_smooth Z Y hZ hY).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have htwice : deriv (fun y => 2 * P y) x = 2 * deriv P x :=
    (((hP.differentiable (by simp)) x).hasDerivAt.const_mul 2).deriv
  have hscale : m62ArcDerivative F c t (fun y => 2 * P y) x =
      2 * m62ArcDerivative F c t P x := by
    dsimp only [m62ArcDerivative]
    rw [htwice]
    ring
  have hpair := m63ArcDerivative_metric_pairing F c hc Z Y hZ hY ht x
  change m62ArcDerivative F c t P x =
    (F.metric t).inner (c x t)
      (m63CurvatureJet F c (i + 2) t x) (m63CurvatureJet F c i t x) +
      m63CurvatureJetSquared F c (i + 1) t x at hpair
  change m62ArcDerivative F c t
    (fun y => m62ArcDerivative F c t (m63CurvatureJetSquared F c i t) y) x = _
  rw [show (fun y => m62ArcDerivative F c t (m63CurvatureJetSquared F c i t) y) =
      (fun y => 2 * P y) from funext hArc, hscale, hpair]
  ring

theorem m63CurvatureJet_one_tangent
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    (F.metric t).inner (c x t) (m63CurvatureJet F c 1 t x)
      (spatialUnitTangent F c t x) = -m62CurvatureSquared F c t x := by
  have hpair := m63ArcDerivative_metric_pairing F c hc
    (fun z => m62CurvatureVector F c z.2 z.1)
    (fun z => spatialUnitTangent F c z.2 z.1)
    (curvature_joint_contMDiff F c hc) (unitTangent_joint_contMDiff F c hc) ht x
  have hzero : (fun y => (F.metric t).inner (c y t)
      (m62CurvatureVector F c t y) (spatialUnitTangent F c t y)) =
      (fun _ : ℝ => 0) := by
    funext y
    exact curvature_unitTangent_inner_zero F c hc (Ioo_subset_Icc_self ht) y
  rw [hzero, m62ArcDerivative, deriv_const, mul_zero] at hpair
  change 0 = (F.metric t).inner (c x t) (m63CurvatureJet F c 1 t x)
    (spatialUnitTangent F c t x) + m62CurvatureSquared F c t x at hpair
  linarith

theorem m63CurvatureJetSquared_periodic [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) :
    Function.Periodic (m63CurvatureJetSquared F c i t) curvePeriod := by
  have hfreeze (d : ℝ → ℝ → M) (j : ℕ) :
      (fun y => m63CurvatureJet F d j t y) =
        (fun y => m63CurvatureJet F (fun z _ => d z t) j t y) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      funext y
      change m62SpatialDerivative F d t (fun z => m63CurvatureJet F d j t z) y =
        m62SpatialDerivative F (fun z _ => d z t) t
          (fun z => m63CurvatureJet F (fun w _ => d w t) j t z) y
      rw [ih]
      rfl
  have hsq (d : ℝ → ℝ → M) (y : ℝ) :
      m63CurvatureJetSquared F d i t y =
        m63CurvatureJetSquared F (fun z _ => d z t) i t y := by
    dsimp only [m63CurvatureJetSquared]
    rw [congrFun (hfreeze d i) y]
  have hpos (y : ℝ) : 0 < deriv (fun z : ℝ => z + curvePeriod) y := by
    have hd : HasDerivAt (fun z : ℝ => z + curvePeriod) 1 y :=
      (hasDerivAt_id y).add_const curvePeriod
    rw [hd.deriv]
    norm_num
  intro x
  have htransport := M63.smooth_curvatureJetSquared_comp F c hc
    (differentiable_id.add_const curvePeriod) hpos ht i x
  have hslice : (fun y _ : ℝ => c (y + curvePeriod) t) =
      (fun y _ : ℝ => c y t) := by
    funext y s
    exact hc.periodic t (Ioo_subset_Icc_self ht) y
  calc
    m63CurvatureJetSquared F c i t (x + curvePeriod) =
        m63CurvatureJetSquared F (fun y s => c (y + curvePeriod) s) i t x :=
      htransport.symm
    _ = m63CurvatureJetSquared F (fun y _ => c (y + curvePeriod) t) i t x := hsq _ x
    _ = m63CurvatureJetSquared F (fun y _ => c y t) i t x := by rw [hslice]
    _ = m63CurvatureJetSquared F c i t x := (hsq c x).symm

end PoincareConjecture
