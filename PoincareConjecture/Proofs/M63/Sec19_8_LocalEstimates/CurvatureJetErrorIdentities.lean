import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetSpatialCalculus
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTimeRegularity

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63CurvatureJetSquared_hasDerivAt [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let J := m63CurvatureJet F c i t x
    let T := rampHorizontalCovariantDerivative D (fun r => c x r)
      (fun r => m63CurvatureJet F c i r x) t
    HasDerivAt (fun r => m63CurvatureJetSquared F c i r x)
      (-2 * D.ricci (c x t) J J + 2 * (F.metric t).inner (c x t) T J) t := by
  let D := F.connection t
  let J := m63CurvatureJet F c i t x
  let T := rampHorizontalCovariantDerivative D (fun r => c x r)
    (fun r => m63CurvatureJet F c i r x) t
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun r : ℝ => (x, r)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => c x r) t :=
    ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime
  have hjoint := M63.curvatureJet_joint_contMDiff F c hc i
  have hjet : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun r => (⟨c x r, m63CurvatureJet F c i r x⟩ : TangentBundle (𝓡 n) M)) t :=
    ((hjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime
  apply (hasDerivAt_flow_metric_pairing F ht hcurve hjet hjet).congr_deriv
  change -2 * D.ricci (c x t) J J + (F.metric t).inner (c x t) T J +
    (F.metric t).inner (c x t) J T =
      -2 * D.ricci (c x t) J J + 2 * (F.metric t).inner (c x t) T J
  rw [(F.metric t).symm (c x t) J T]
  ring

theorem m63CurvatureJetSquared_diffusion_identity [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let J := m63CurvatureJet F c i t x
    let T := rampHorizontalCovariantDerivative D (fun r => c x r)
      (fun r => m63CurvatureJet F c i r x) t
    let Q := T - m63CurvatureJet F c (i + 2) t x
    deriv (fun r => m63CurvatureJetSquared F c i r x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c i t) x =
      -2 * m63CurvatureJetSquared F c (i + 1) t x -
        2 * D.ricci (c x t) J J + 2 * (F.metric t).inner (c x t) Q J := by
  have htime := (m63CurvatureJetSquared_hasDerivAt F c hc i ht x).deriv
  dsimp only at htime ⊢
  rw [htime, m63CurvatureJetSquared_arcSecond_eq F c hc i ht x]
  simp only [map_sub, sub_apply]
  ring

theorem m63CurvatureJet_diffusionError_succ_pair [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (Z : TangentSpace (𝓡 n) (c x t)) :
    let D := F.connection t
    let J : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
      fun j y => m63CurvatureJet F c j t y
    let T : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
      fun j y => rampHorizontalCovariantDerivative D (fun r => c y r)
        (fun r => m63CurvatureJet F c j r y) t
    let Q : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
      fun j y => T j y - J (j + 2) y
    let S := spatialUnitTangent F c t x
    let H := m62CurvatureVector F c t x
    let A := m62TangentRicci F c t x + m62CurvatureSquared F c t x
    (F.metric t).inner (c x t) (Q (i + 1) x) Z =
      (F.metric t).inner (c x t) (m62SpatialDerivative F c t (Q i) x) Z +
        A * (F.metric t).inner (c x t) (J (i + 1) x) Z +
        D.curvatureTensor (c x t) H S Z (J i x) -
        D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, J i x, Z] -
        D.covariantTensorDerivative D.ricciEvaluation (c x t) ![J i x, S, Z] +
        D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, J i x] := by
  let D := F.connection t
  let J : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun j y => m63CurvatureJet F c j t y
  let T : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun j y => rampHorizontalCovariantDerivative D (fun r => c y r)
      (fun r => m63CurvatureJet F c j r y) t
  let Q : (j : ℕ) → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun j y => T j y - J (j + 2) y
  let S := spatialUnitTangent F c t x
  let H := m62CurvatureVector F c t x
  let A := m62TangentRicci F c t x + m62CurvatureSquared F c t x
  let Y : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun z => m63CurvatureJet F c i z.2 z.1
  have hY := M63.curvatureJet_joint_contMDiff F c hc i
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hspace : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun y : ℝ => (y, t)) x :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hTjoint := m63FixedPullback_time_joint_contMDiff D c Y hopen hc.joint_smooth hY
  have hTspace : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, T i y⟩ : TangentBundle (𝓡 n) M)) x :=
    ((hTjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace
  have hJjoint := M63.curvatureJet_joint_contMDiff F c hc (i + 2)
  have hJspace : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, J (i + 2) y⟩ : TangentBundle (𝓡 n) M)) x :=
    ((hJjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp x hspace
  have hJneg : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, -J (i + 2) y⟩ : TangentBundle (𝓡 n) M)) x := by
    have hcoord := hJspace
    rw [mdifferentiableAt_totalSpace] at hcoord ⊢
    refine ⟨hcoord.1, ?_⟩
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c x t)
    have hnear : ∀ᶠ y in 𝓝 x, c y t ∈ e.baseSet :=
      hcoord.1.continuousAt (e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (c x t)))
    apply hcoord.2.neg.congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    change (e ⟨c y t, -J (i + 2) y⟩).2 = -(e ⟨c y t, J (i + 2) y⟩).2
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hy] using
      (e.continuousLinearMapAt ℝ (c y t)).map_neg (J (i + 2) y)
  have hnegDerivative :
      rampHorizontalCovariantDerivative D (fun y => c y t)
        (fun y => -J (i + 2) y) x =
      -rampHorizontalCovariantDerivative D (fun y => c y t) (J (i + 2)) x := by
    simpa only [neg_one_smul, zero_smul, zero_add] using
      pullback_smul D (hasDerivAt_const x (-1 : ℝ)) hJspace
  have hsubtract : m62SpatialDerivative F c t (Q i) x =
      m62SpatialDerivative F c t (T i) x - J (i + 3) x := by
    change m62SpatialDerivative F c t (fun y => T i y - J (i + 2) y) x =
      m62SpatialDerivative F c t (T i) x -
        m62SpatialDerivative F c t (J (i + 2)) x
    simp only [m62SpatialDerivative, sub_eq_add_neg]
    rw [pullback_add D hTspace hJneg, hnegDerivative]
    simp only [smul_add, smul_neg, D]
  have hcomm := m63SpatialDerivative_time_commutator_pair F c hc Y hY ht x Z
  change (F.metric t).inner (c x t) (T (i + 1) x) Z =
    (F.metric t).inner (c x t) (m62SpatialDerivative F c t (T i) x) Z +
      A * (F.metric t).inner (c x t) (J (i + 1) x) Z +
      D.curvatureTensor (c x t) H S Z (J i x) -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, J i x, Z] -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![J i x, S, Z] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, J i x] at hcomm
  change (F.metric t).inner (c x t) (Q (i + 1) x) Z =
    (F.metric t).inner (c x t) (m62SpatialDerivative F c t (Q i) x) Z +
      A * (F.metric t).inner (c x t) (J (i + 1) x) Z +
      D.curvatureTensor (c x t) H S Z (J i x) -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, J i x, Z] -
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![J i x, S, Z] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t) ![Z, S, J i x]
  rw [hsubtract]
  change (F.metric t).inner (c x t) (T (i + 1) x - J (i + 3) x) Z = _
  simp only [map_sub, sub_apply]
  rw [hcomm]
  ring

end PoincareConjecture
