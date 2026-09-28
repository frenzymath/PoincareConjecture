import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.FirstJetTimePair










set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem m63FirstJetSquared_evolution [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let R := D.riemannEvaluation
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let J := D.covariantTensorDerivative R
    let S := spatialUnitTangent F c t x
    let H := m63CurvatureJet F c 0 t x
    let B := m63CurvatureJet F c 1 t x
    let C := m63CurvatureJet F c 2 t x
    let q := m62CurvatureSquared F c t x
    let beta := m63CurvatureJetSquared F c 1 t x
    let chi := m63CurvatureJetSquared F c 2 t x
    let N := (F.metric t).inner (c x t) H B
    let r := m62TangentRicci F c t
    let E := J (c x t) ![S, H, S, B, S] + R (c x t) ![B, S, B, S] +
      2 * R (c x t) ![H, S, B, H] - 2 * U (c x t) ![S, S, S, B] +
      U (c x t) ![S, B, S, S] - 3 * T (c x t) ![H, S, B] -
      3 * T (c x t) ![S, H, B] + 3 * T (c x t) ![B, S, H]
    deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
        m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x =
      -2 * chi - 2 * D.ricci (c x t) B B + (2 * q + 6 * r x) * beta +
        12 * N ^ 2 + 6 * m62ArcDerivative F c t r x * N -
        4 * q * (F.metric t).inner (c x t) C H -
        2 * q * m62ArcSecondDerivative F c t r x + 2 * E := by
  let D := F.connection t
  let R := D.riemannEvaluation
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let J := D.covariantTensorDerivative R
  let S := spatialUnitTangent F c t x
  let H := m63CurvatureJet F c 0 t x
  let B := m63CurvatureJet F c 1 t x
  let C := m63CurvatureJet F c 2 t x
  let q := m62CurvatureSquared F c t
  let r := m62TangentRicci F c t
  let A : ℝ → ℝ := fun y => r y + q y
  let beta := m63CurvatureJetSquared F c 1 t x
  let chi := m63CurvatureJetSquared F c 2 t x
  let N := (F.metric t).inner (c x t) H B
  let E := J (c x t) ![S, H, S, B, S] + R (c x t) ![B, S, B, S] +
    2 * R (c x t) ![H, S, B, H] - 2 * U (c x t) ![S, S, S, B] +
    U (c x t) ![S, B, S, S] - 3 * T (c x t) ![H, S, B] -
    3 * T (c x t) ![S, H, B] + 3 * T (c x t) ![B, S, H]
  let DTB := rampHorizontalCovariantDerivative D (fun s => c x s)
    (fun s => m63CurvatureJet F c 1 s x) t
  change deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
      m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x =
    -2 * chi - 2 * D.ricci (c x t) B B + (2 * q x + 6 * r x) * beta +
      12 * N ^ 2 + 6 * m62ArcDerivative F c t r x * N -
      4 * q x * (F.metric t).inner (c x t) C H -
      2 * q x * m62ArcSecondDerivative F c t r x + 2 * E
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) (fun s : ℝ => (x, s)) t :=
    ((differentiableAt_const x).prodMk differentiableAt_id).mdifferentiableAt
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun s => c x s) t :=
    ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt
      (by simp)).comp t htime
  have hBjoint := M63.curvatureJet_joint_contMDiff F c hc 1
  have hBtime : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨c x s, m63CurvatureJet F c 1 s x⟩ : TangentBundle (𝓡 n) M)) t :=
    ((hBjoint.contMDiffAt (hopen.mem_nhds hmem)).mdifferentiableAt (by simp)).comp t htime
  have hdt := (hasDerivAt_flow_metric_pairing F ht hcurve hBtime hBtime).deriv
  change deriv (fun s => m63CurvatureJetSquared F c 1 s x) t =
    -2 * D.ricci (c x t) B B + (F.metric t).inner (c x t) DTB B +
      (F.metric t).inner (c x t) B DTB at hdt
  rw [(F.metric t).symm (c x t) B DTB] at hdt
  have hpair := m63FirstJet_time_self_pair F c hc ht x
  change (F.metric t).inner (c x t) DTB B =
    (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) B +
      3 * A x * beta + 3 * m62ArcDerivative F c t A x * N +
      m62ArcSecondDerivative F c t A x * (F.metric t).inner (c x t) S B + E at hpair
  have hspace := m63CurvatureJetSquared_arcSecond_eq F c hc 1 ht x
  change m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x =
    2 * (F.metric t).inner (c x t) (m63CurvatureJet F c 3 t x) B + 2 * chi at hspace
  have hevolution : deriv (fun s => m63CurvatureJetSquared F c 1 s x) t -
      m62ArcSecondDerivative F c t (m63CurvatureJetSquared F c 1 t) x =
    -2 * chi - 2 * D.ricci (c x t) B B + 6 * A x * beta +
      6 * m62ArcDerivative F c t A x * N +
      2 * m62ArcSecondDerivative F c t A x * (F.metric t).inner (c x t) S B + 2 * E := by
    rw [hdt, hspace]
    simp only [hpair]
    ring
  have hA : ContDiff ℝ ∞ A :=
    (normalization_coefficient_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hq : ContDiff ℝ ∞ q :=
    (curvatureSquared_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hr : ContDiff ℝ ∞ r := by
    have heq : (fun y => A y - q y) = r := by
      funext y
      dsimp only [A]
      ring
    have h : ContDiff ℝ ∞ (fun y => A y - q y) := hA.sub hq
    rwa [heq] at h
  have hv : ContDiff ℝ ∞ (curveSpeed F c t) :=
    (speed_joint_contDiffOn F c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hvi := hv.inv (fun y => (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne')
  have hqarc : ContDiff ℝ ∞ (m62ArcDerivative F c t q) :=
    hvi.mul (contDiff_infty_iff_deriv.mp hq).2
  have hrarc : ContDiff ℝ ∞ (m62ArcDerivative F c t r) :=
    hvi.mul (contDiff_infty_iff_deriv.mp hr).2
  have hsplit (y : ℝ) : m62ArcDerivative F c t A y =
      m62ArcDerivative F c t r y + m62ArcDerivative F c t q y := by
    have hd : HasDerivAt A (deriv r y + deriv q y) y :=
      ((hr.differentiable (by simp) y).hasDerivAt).add
        (hq.differentiable (by simp) y).hasDerivAt
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  have hsplit2 : m62ArcSecondDerivative F c t A x =
      m62ArcSecondDerivative F c t r x + m62ArcSecondDerivative F c t q x := by
    have hd : HasDerivAt
        (fun y => m62ArcDerivative F c t r y + m62ArcDerivative F c t q y)
        (deriv (m62ArcDerivative F c t r) x + deriv (m62ArcDerivative F c t q) x) x :=
      ((hrarc.differentiable (by simp) x).hasDerivAt).add
        (hqarc.differentiable (by simp) x).hasDerivAt
    change m62ArcDerivative F c t (fun y => m62ArcDerivative F c t A y) x = _
    rw [show (fun y => m62ArcDerivative F c t A y) =
      (fun y => m62ArcDerivative F c t r y + m62ArcDerivative F c t q y) from funext hsplit]
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcSecondDerivative, m62ArcDerivative]
    ring
  have hqfirst : m62ArcDerivative F c t q x = 2 * N := by
    have hH := M63.curvatureJet_joint_contMDiff F c hc 0
    have h := m63ArcDerivative_metric_pairing F c hc
      (fun z => m63CurvatureJet F c 0 z.2 z.1)
      (fun z => m63CurvatureJet F c 0 z.2 z.1) hH hH ht x
    change m62ArcDerivative F c t q x =
      (F.metric t).inner (c x t) B H + (F.metric t).inner (c x t) H B at h
    rw [(F.metric t).symm (c x t) B H] at h
    dsimp only [N]
    linarith only [h]
  have hqsecond := m63CurvatureJetSquared_arcSecond_eq F c hc 0 ht x
  change m62ArcSecondDerivative F c t q x =
    2 * (F.metric t).inner (c x t) C H + 2 * beta at hqsecond
  have htangent : (F.metric t).inner (c x t) S B = -q x := by
    rw [(F.metric t).symm (c x t) S B]
    exact m63CurvatureJet_one_tangent F c hc ht x
  rw [hsplit, hsplit2, hqfirst, hqsecond, htangent] at hevolution
  dsimp only [A] at hevolution
  rw [hevolution]
  ring

end PoincareConjecture
