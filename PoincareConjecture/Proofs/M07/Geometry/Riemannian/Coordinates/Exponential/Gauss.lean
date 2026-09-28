import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.LocalInverse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialJacobi













noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}



private theorem fderiv_metric_pairing
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (hinv : (B x).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ u v, B y u v = B y v u) (a b c : E) :
    fderiv ℝ (fun y => B y a b) x c =
      B x (coordinateChristoffel B x c a) b +
        B x a (coordinateChristoffel B x c b) := by
  have hD (u v d : E) :
      fderiv ℝ (fun y => B y u v) x d = fderiv ℝ B x d u v := by
    have h := (hB.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
      (hasFDerivAt_const v x)
    simpa using congrArg (fun L => L d) h.fderiv
  have hK (u v w : E) :
      B x (coordinateChristoffel B x u v) w =
        (2⁻¹ : ℝ) *
          (fderiv ℝ B x u v w + fderiv ℝ B x v w u -
            fderiv ℝ B x w u v) := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L w)
      (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B x) u v))
    simpa [coordinateChristoffel, metricKoszulCovector] using h
  have hsymm' (u v w : E) : fderiv ℝ B x u v w = fderiv ℝ B x u w v := by
    rw [← hD v w u, ← hD w v u]
    have heq : (fun y => B y v w) =ᶠ[𝓝 x] (fun y => B y w v) :=
      hsymm.mono (fun y hy => hy v w)
    exact congrArg (fun L : E →L[ℝ] ℝ => L u) heq.fderiv_eq
  rw [hD a b c, hsymm.self_of_nhds a (coordinateChristoffel B x c b),
    hK c a b, hK c b a, hsymm' c b a, hsymm' a b c, hsymm' b a c]
  ring

namespace LocalFlowData

variable (D : LocalFlowData B U x)

private theorem trajectory_energy
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u)
    {v : E} (hv : v ∈ D.domain) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    B (D.trajectory v t).1 (D.trajectory v t).2 (D.trajectory v t).2 = B x v v := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun r => B (D.trajectory v r).1
        (D.trajectory v r).2 (D.trajectory v r).2) 0 s := by
    have hm := D.trajectory_mem hv hs
    exact hasDerivAt_coordinate_geodesic_energy
      ((hB.contDiffAt (hU.mem_nhds hm)).differentiableAt (by simp))
      (hinv _ hm) (hsymm _ hm) (D.trajectory_hasDerivAt hv hs).fst
      (D.trajectory_hasDerivAt hv hs).snd
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-2 : ℝ) 2).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  simpa only [D.trajectory_initial hv] using hc

private theorem hasDerivAt_geodesic_pairing
    {q u J : ℝ → E} {K : E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (q t)) (hinv : (B (q t)).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (q t), ∀ a b, B y a b = B y b a)
    (hq : HasDerivAt q (u t) t)
    (hu : HasDerivAt u (-coordinateChristoffel B (q t) (u t) (u t)) t)
    (hJ : HasDerivAt J K t) :
    HasDerivAt (fun s => B (q s) (u s) (J s))
      ((2⁻¹ : ℝ) * fderiv ℝ B (q t) (J t) (u t) (u t) + B (q t) (u t) K) t := by
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := B) t hB.hasFDerivAt hq
  have houter := (hcomp.clm_apply hu).clm_apply hJ
  apply houter.congr_deriv
  simp only [Function.comp_apply, add_apply, neg_apply, map_neg]
  have hD (a b c : E) : fderiv ℝ (fun y => B y a b) (q t) c =
      fderiv ℝ B (q t) c a b := by
    simpa using congrArg (fun L => L c)
      ((hB.hasFDerivAt.clm_apply (hasFDerivAt_const a (q t))).clm_apply
        (hasFDerivAt_const b (q t))).fderiv
  have hsymm' : fderiv ℝ B (q t) (u t) (J t) (u t) =
      fderiv ℝ B (q t) (u t) (u t) (J t) := by
    rw [← hD, ← hD]
    have heq : (fun y => B y (J t) (u t)) =ᶠ[𝓝 (q t)]
        (fun y => B y (u t) (J t)) :=
      hsymm.mono (fun _ h => h (J t) (u t))
    exact congrArg (fun L : E →L[ℝ] ℝ => L (u t)) heq.fderiv_eq
  have hK := congrArg (fun L : E →L[ℝ] ℝ => L (J t))
    (hinv.self_apply_inverse (metricKoszulCovector (fderiv ℝ B (q t)) (u t) (u t)))
  change B (q t) (coordinateChristoffel B (q t) (u t) (u t)) (J t) = _ at hK
  simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul] at hK
  rw [hsymm'] at hK
  rw [hK]
  ring

private theorem radial_pairing_hasDerivAt
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u)
    {v : E} (hv : v ∈ D.domain) (w : E)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun r => B (D.trajectory v r).1 (D.trajectory v r).2
      (variationField (D.radialGeodesicVariation hv w) r)) (B x v w) t := by
  let F := D.radialGeodesicVariation hv w
  let J := variationField F
  let K := fderiv ℝ (fun s => (F.phase (s, t)).2) 0 1
  have hF : ContDiffAt ℝ ∞ F.phase (0, t) :=
    F.smooth.contDiffAt (((D.isOpen_radialParameterDomain v w).prod isOpen_Ioo).mem_nhds
      ⟨D.zero_mem_radialParameterDomain hv w, ht⟩)
  have hs : ContDiffAt ℝ ∞ (fun s => F.phase (s, t)) 0 :=
    hF.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hqs : HasDerivAt (fun s => (F.phase (s, t)).1) (J t) 0 :=
    (hs.fst.differentiableAt (by simp)).hasDerivAt
  have hus : HasDerivAt (fun s => (F.phase (s, t)).2) K 0 :=
    (hs.snd.differentiableAt (by simp)).hasDerivAt
  have hmixed : HasDerivAt J K t := by
    have hswap : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (F.phase (p.2, p.1)).1) (t, 0) :=
      ContDiffAt.comp (f := fun p : ℝ × ℝ => (p.2, p.1))
        (g := fun p => (F.phase p).1) (t, 0) hF.fst
        (contDiffAt_snd.prodMk contDiffAt_fst)
    apply Poincare.Analysis.hasDerivAt_fderiv_time_of_eventually hswap
    filter_upwards [(D.isOpen_radialParameterDomain v w).mem_nhds
      (D.zero_mem_radialParameterDomain hv w)] with s hs
    exact (F.geodesic s hs t ht).fst
  have hm := D.trajectory_mem hv ht
  have hBt : DifferentiableAt ℝ B (D.trajectory v t).1 :=
    (hB.contDiffAt (hU.mem_nhds hm)).differentiableAt (by simp)
  have hsymm_nhds : ∀ᶠ y in 𝓝 (D.trajectory v t).1, ∀ a b, B y a b = B y b a := by
    filter_upwards [hU.mem_nhds hm] with y hy
    exact hsymm y hy
  have hp := hasDerivAt_geodesic_pairing
    (q := fun r => (D.trajectory v r).1) (u := fun r => (D.trajectory v r).2)
    hBt (hinv _ hm) hsymm_nhds
    (D.trajectory_hasDerivAt hv ht).fst (D.trajectory_hasDerivAt hv ht).snd hmixed
  apply hp.congr_deriv
  have hbase : F.phase (0, t) = D.trajectory v t := by
    simp [F, radialGeodesicVariation]
  have hBt' : DifferentiableAt ℝ B (F.phase (0, t)).1 := by rwa [hbase]
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := B) 0 hBt'.hasFDerivAt hqs
  have henergy := (hcomp.clm_apply hus).clm_apply hus
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hinit := ((hasDerivAt_const (0 : ℝ) (B x)).clm_apply hline).clm_apply hline
  have heq : (fun s => B (F.phase (s, t)).1 (F.phase (s, t)).2 (F.phase (s, t)).2) =ᶠ[𝓝 0]
      (fun s : ℝ => B x (v + s • w) (v + s • w)) := by
    filter_upwards [(D.isOpen_radialParameterDomain v w).mem_nhds
      (D.zero_mem_radialParameterDomain hv w)] with s hs
    exact D.trajectory_energy hU hB hinv hsymm hs ht
  have hval := henergy.unique (hinit.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply, add_apply, zero_apply, zero_smul,
    add_zero, zero_add, hbase] at hval
  rw [hsymm _ hm K (D.trajectory v t).2] at hval
  have hx : x ∈ U := by
    have hm0 := D.trajectory_mem hv (t := 0) (by norm_num)
    simpa [D.trajectory_initial hv] using hm0
  rw [hsymm x hx w v] at hval
  dsimp [K] at hval ⊢
  linarith

private theorem exponential_radial_derivative {v : E} (hv : v ∈ D.domain) :
    fderiv ℝ D.exponential v v = (D.trajectory v 1).2 := by
  have heq (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      D.exponential (s • v) = (D.trajectory v s).1 := by
    have h := congrArg Prod.fst (D.scaling (c := s)
      (by rw [abs_of_nonneg hs.1]; exact hs.2) hv D.time_mem)
    simpa only [exponential, endpoint, trajectory, velocityScale_fst,
      smul_comm D.time⁻¹ s, mul_comm s D.time] using h
  have hd := (D.smooth_exponential.contDiffAt (D.isOpen_domain.mem_nhds hv)).differentiableAt
    (by simp)
  have hline : HasDerivAt (fun s : ℝ => s • v) v 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hrad : HasDerivAt (fun s : ℝ => D.exponential (s • v))
      (fderiv ℝ D.exponential v v) 1 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 1 hline (by simp)
  have htime : HasDerivAt (fun s => (D.trajectory v s).1) (D.trajectory v 1).2 1 :=
    (D.trajectory_hasDerivAt hv (by norm_num)).fst
  have hwithin := htime.hasDerivWithinAt.congr heq (heq 1 (by norm_num))
  have huniq := uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num) 1 (by norm_num)
  exact (hrad.hasDerivWithinAt.derivWithin huniq).symm.trans (hwithin.derivWithin huniq)


theorem gauss_identity
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u)
    {v : E} (hv : v ∈ D.domain) (w : E) :
    B (D.exponential v) (fderiv ℝ D.exponential v v)
      (fderiv ℝ D.exponential v w) = B x v w := by
  let P := fun r => B (D.trajectory v r).1 (D.trajectory v r).2
    (variationField (D.radialGeodesicVariation hv w) r)
  have hd (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun r => P r - r * B x v w) 0 t := by
    convert! (D.radial_pairing_hasDerivAt hU hB hinv hsymm hv w ht).sub
      ((hasDerivAt_id t).mul_const (B x v w)) using 1
    simp
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-2 : ℝ) 2).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv)
    (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
    (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
  simp only [P, D.radialGeodesicVariation_initial hv w, map_zero,
    D.radialGeodesicVariation_endpoint hv w, D.trajectory_endpoint,
    ← D.exponential_radial_derivative hv, one_mul, zero_mul, sub_self] at hc
  exact sub_eq_zero.mp hc


theorem gauss_identity_at_zero
    {w : E} :
    B (D.exponential 0) (fderiv ℝ D.exponential 0 (0 : E))
        (fderiv ℝ D.exponential 0 w) = B x 0 w := by
  have hfd := D.hasFDerivAt_exponential_zero
  have hzero := D.exponential_zero
  rw [hzero]
  rw [hfd.fderiv]
  simp

end LocalFlowData

section Gauss

variable [FiniteDimensional ℝ E]






theorem exists_local_exponential_gauss
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ u v, B y u v = B y v u) (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph E E,
      (0 : E) ∈ e.source ∧ e 0 = x ∧ e.target ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ v ∈ e.source, ∀ w : E,
        B (e v) (fderiv ℝ (e : E → E) v v)
            (fderiv ℝ (e : E → E) v w) = B x v w := by
  obtain ⟨D⟩ := exists_localFlowData hU hB hinv hsymm hx
  obtain ⟨e, hzero, hsource, heq, hsmooth, _⟩ := D.exists_openPartialHomeomorph
  have hezero : e 0 = x := by rw [heq]; exact D.exponential_zero
  have htarget : e.target ⊆ U := by
    intro y hy
    have h := D.trajectory_mem (hsource (e.map_target hy)) (t := 1) (by norm_num)
    rwa [D.trajectory_endpoint, ← heq, e.right_inv hy] at h
  refine ⟨e, hzero, hezero, htarget, hsmooth, ?_, ?_⟩
  · rw [heq]
    exact D.hasFDerivAt_exponential_zero
  intro v hv w
  rw [heq]
  exact D.gauss_identity hU hB hinv hsymm (hsource hv) w

end Gauss

end PoincareConjecture.CoordinateExponential
