
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport.Regularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Extend









open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem spatial_fderiv_eq
    {f : P × ℝ → G} {q : P × ℝ} (hf : DifferentiableAt ℝ f q) :
    fderiv ℝ (fun x => f (x, q.2)) q.1 =
      (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ P ℝ) := by
  exact (hf.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)).fderiv

private theorem hasDerivAt_fderiv_param_of_contDiffOn
    {f : P × ℝ → G} {g : P × ℝ → G} {U : Set P} (hU : IsOpen U)
    {T : Set ℝ} (hT : IsOpen T)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ T))
    (ht : ∀ q ∈ U ×ˢ T, HasDerivAt (fun t => f (q.1, t)) (g q) q.2)
    {x : P} (hx : x ∈ U) {t : ℝ} (htmem : t ∈ T) :
    HasDerivAt (fun t => fderiv ℝ (fun p => f (p, t)) x)
      (fderiv ℝ (fun p => g (p, t)) x) t := by
  let j := ContinuousLinearMap.inl ℝ P ℝ
  let e : P × ℝ := (0, 1)
  let D := fderiv ℝ (fderiv ℝ f) (x, t)
  have hopen : IsOpen (U ×ˢ T) := hU.prod hT
  have hp : (x, t) ∈ U ×ˢ T := ⟨hx, htmem⟩
  have hfd : ∀ q ∈ U ×ˢ T, DifferentiableAt ℝ f q := fun q hq =>
    ((hf q hq).contDiffAt (hopen.mem_nhds hq)).differentiableAt (by simp)
  have hD : HasFDerivAt (fderiv ℝ f) D (x, t) :=
    (((hf _ hp).contDiffAt (hopen.mem_nhds hp)).fderiv_right
      (m := 1) (by decide)).differentiableAt
        (by simp) |>.hasFDerivAt
  have htime : HasDerivAt (fun s => fderiv ℝ f (x, s)) (D e) t := by
    exact hD.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have htimej : HasDerivAt (fun s => (fderiv ℝ f (x, s)).comp j) ((D e).comp j) t := by
    simpa using htime.clm_comp (hasDerivAt_const t j)
  have htimeeq : (fun s => (fderiv ℝ f (x, s)).comp j) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ (fun p => f (p, s)) x) := by
    filter_upwards [hT.mem_nhds htmem] with s hs
    exact (spatial_fderiv_eq (hfd (x, s) ⟨hx, hs⟩)).symm
  have hgeq : (fun p => (fderiv ℝ f (p, t)) e) =ᶠ[𝓝 x]
      (fun p => g (p, t)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hcurve : HasDerivAt (fun s : ℝ => (y, s)) e t :=
      (hasDerivAt_const t y).prodMk (hasDerivAt_id t)
    have hd := (hfd (y, t) ⟨hy, htmem⟩).hasFDerivAt.comp_hasDerivAt t hcurve
    exact hd.unique (ht (y, t) ⟨hy, htmem⟩)
  have hgderiv : HasFDerivAt (fun p => g (p, t)) ((D.flip e).comp j) x := by
    have h1 := (hD.clm_apply (hasFDerivAt_const (𝕜 := ℝ) e (x, t))).comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    have h2 : HasFDerivAt (fun p => (fderiv ℝ f (p, t)) e) ((D.flip e).comp j) x := by
      simpa [j, Function.comp_def] using h1
    exact h2.congr_of_eventuallyEq hgeq.symm
  have hsymm : (D e).comp j = (D.flip e).comp j := by
    ext v
    exact ((hf _ hp).contDiffAt (hopen.mem_nhds hp)).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide) e (j v)
  rw [hgderiv.fderiv, ← hsymm]
  exact htimej.congr_of_eventuallyEq htimeeq.symm

private theorem hasDerivWithinAt_Icc_of_continuousOn
    {f g : ℝ → G} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt f (g s) s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt f (g t) (Icc a b) t := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hc : ∀ s ∈ closure (Ioo a b), ContinuousWithinAt f (Ioo a b) s := by
    intro s hs
    rw [hcl] at hs
    exact (hf s hs).mono Ioo_subset_Icc_self
  have hlim : Tendsto (fun s => fderiv ℝ f s) (𝓝[Ioo a b] t)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (g t))) := by
    have hcont : ContinuousWithinAt (fun s => ContinuousLinearMap.toSpanSingleton ℝ (g s))
        (Icc a b) t :=
      ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp_continuousWithinAt
        (hg t ht)
    apply (hcont.mono Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hd s hs).hasFDerivAt.fderiv.symm
  have hfderiv := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo hc hlim
  rw [hcl] at hfderiv
  simpa using hfderiv.hasDerivWithinAt



theorem linearODE_hasDerivWithinAt_fderiv_param
    [FiniteDimensional ℝ P] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t)
    {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => fderiv ℝ (fun p => Φ p s) x)
      ((fderiv ℝ (fun p => A p t) x).flip (Φ x t) +
        (A x t).comp (fderiv ℝ (fun p => Φ p t) x)) (Icc a b) t := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    simp only [Icc_self] at *
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact HasFDerivWithinAt.singleton
  let DΦ : P × ℝ → P →L[ℝ] G := fun q => fderiv ℝ (fun p => Φ p q.2) q.1
  let DA : P × ℝ → P →L[ℝ] G →L[ℝ] G := fun q => fderiv ℝ (fun p => A p q.2) q.1
  let R : P × ℝ → P →L[ℝ] G := fun q =>
    (DA q).flip (Φ q.1 q.2) + (A q.1 q.2).comp (DΦ q)
  have hΦcont := linearODE_continuousOn A hab hU hA Φ hinit hsol
  have hDΦcont : ContinuousOn DΦ (U ×ˢ Icc a b) :=
    linearODE_continuousOn_fderiv_param A hab hU hA Φ hinit hsol
  have hDAcont : ContinuousOn DA (U ×ˢ Icc a b) :=
    (contDiffOn_fderiv_param_Icc hlt hU hA).continuousOn
  have hRcont : ContinuousOn R (U ×ˢ Icc a b) := by
    exact ((ContinuousLinearMap.flipₗᵢ ℝ P G G).continuous.comp_continuousOn hDAcont).clm_apply
      hΦcont |>.add (hA.continuousOn.clm_comp hDΦcont)
  have hslice : ContinuousOn (fun s : ℝ => (x, s)) (Icc a b) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : MapsTo (fun s : ℝ => (x, s)) (Icc a b) (U ×ˢ Icc a b) :=
    fun _ hs => ⟨hx, hs⟩
  change HasDerivWithinAt (fun s => DΦ (x, s)) (R (x, t)) (Icc a b) t
  apply hasDerivWithinAt_Icc_of_continuousOn hlt
    (hDΦcont.comp hslice hmaps) (hRcont.comp hslice hmaps) ?_ ht
  intro s hs
  have hΦsmooth := linearODE_contDiffOn_interior A hab hU hA Φ hinit hsol
  have hd := hasDerivAt_fderiv_param_of_contDiffOn hU isOpen_Ioo hΦsmooth
    (g := fun q => A q.1 q.2 (Φ q.1 q.2))
    (fun q hq => (hsol q.1 hq.1 q.2 (Ioo_subset_Icc_self hq.2)).hasDerivAt
      (Icc_mem_nhds hq.2.1 hq.2.2)) hx hs
  have hAt : ContDiffOn ℝ ∞ (fun p => A p s) U :=
    hA.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hp => ⟨hp, Ioo_subset_Icc_self hs⟩)
  have hΦt := linearODE_contDiffOn_spatial A hab hU hA Φ hinit hsol
    (Ioo_subset_Icc_self hs)
  have hdA := ((hAt x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdΦ := ((hΦt x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hR : fderiv ℝ (fun p => A p s (Φ p s)) x = R (x, s) := by
    rw [(hdA.hasFDerivAt.clm_apply hdΦ.hasFDerivAt).fderiv]
    exact add_comm _ _
  rw [hR] at hd
  exact hd


theorem linearODE_hasDerivWithinAt_fderiv_param_apply
    [FiniteDimensional ℝ P] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hinit : ContDiffOn ℝ ∞ (fun p => Φ p a) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t)
    {x : P} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Icc a b) (v : P) :
    HasDerivWithinAt (fun s => (fderiv ℝ (fun p => Φ p s) x) v)
      ((fderiv ℝ (fun p => A p t) x) v (Φ x t) +
        A x t ((fderiv ℝ (fun p => Φ p t) x) v)) (Icc a b) t := by
  simpa using (linearODE_hasDerivWithinAt_fderiv_param A hab hU hA Φ hinit hsol hx ht).clm_apply
    (hasDerivWithinAt_const t (Icc a b) v)

end PoincareConjecture.RicciFlow.Frame
