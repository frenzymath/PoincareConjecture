import PoincareConjecture.Proofs.M63.Mathlib.ContinuousNormalGraphFamily
import PoincareConjecture.Proofs.M63.Mathlib.ContDiffOrderIsoInverse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessGraphEquation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessGraphCoefficients












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem exists_c2ShrinkingCurve_normalGraph_family
    {F : RicciFlow n M (Icc a b)} {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {N : Set W} (hN : IsOpen N) (heN : range e ⊆ N) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ N) (hret : ∀ p, ρ (e p) = p)
    {s T : ℝ} (_hsT : s < T) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r) {m M0 B radius eps : ℝ}
    (hm : 0 < m) (hM : 0 < M0) (hB : 0 ≤ B)
    (hradius : 0 < radius) (heps : 0 < eps)
    (hlower : ∀ y, m ≤ ‖deriv r y‖) (hupper : ∀ y, ‖deriv r y‖ ≤ M0)
    (hsecond : ∀ y, ‖deriv (deriv r) y‖ ≤ B)
    (hsmall : 2 * B * (eps + M0 * radius) ≤ m ^ 2)
    (hmargin : 4 * eps * M0 ≤ m ^ 2 * radius)
    {eta : ℝ} (heta : 0 ≤ eta) (htrans : 2 * M0 * (eta + B * radius) ≤ m ^ 2)
    (hrper : Function.Periodic r curvePeriod)
    (hclose : ∀ t ∈ Icc s T, ∀ x, ‖e (c x t) - r x‖ < eps)
    (hfirst : ∀ t ∈ Icc s T, ∀ x,
      ‖deriv (fun y => e (c y t)) x - deriv r x‖ ≤ eta) :
    ∃ phi : ℝ → (ℝ ≃o ℝ),
      (∀ t ∈ Icc s T,
        (∀ x, phi t x = selectedCurveFootpoint r radius eps (x, e (c x t))) ∧
        ContDiff ℝ 2 (phi t : ℝ → ℝ) ∧ ContDiff ℝ 2 ((phi t).symm : ℝ → ℝ) ∧
        (∀ x, |phi t x - x| < radius) ∧ (∀ x, 0 < deriv (phi t) x) ∧
        (∀ y, HasDerivAt (phi t).symm ((deriv (phi t) ((phi t).symm y))⁻¹) y ∧
          0 < deriv (phi t).symm y) ∧
        (∀ x, phi t (x + curvePeriod) = phi t x + curvePeriod) ∧
        (∀ y, (phi t).symm (y + curvePeriod) = (phi t).symm y + curvePeriod) ∧
        let U : ℝ → W := fun y => e (c ((phi t).symm y) t) - r y
        ContDiff ℝ 2 U ∧ Function.Periodic U curvePeriod ∧
        (∀ y, ⟪U y, deriv r y⟫ = 0) ∧ ∀ x, e (c x t) = r (phi t x) + U (phi t x)) ∧
      let psi : ℝ → ℝ → ℝ := fun y t => (phi t).symm y
      let q : ℝ → ℝ → M := fun y t => c (psi y t) t
      let U : ℝ → ℝ → W := fun y t => e (q y t) - r y
      let V : ℝ → ℝ → W := fun y t => deriv (fun z => e (q z t)) y
      let A : ℝ → ℝ → ℝ := fun y t => ambientCurvePrincipal F ρ t (e (q y t)) (V y t)
      let Bgraph : ℝ → ℝ → W := fun y t => curveGraphLower (A y t)
        (ambientCurveLower F e ρ t (e (q y t)) (V y t))
        (deriv r y) (deriv (deriv r) y) (deriv (deriv (deriv r)) y)
        (U y t) (deriv (fun z => U z t) y)
      ContinuousOn (Function.uncurry psi) (univ ×ˢ Icc s T) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (fun y => psi y z.2) z.1)
        (univ ×ˢ Icc s T) ∧
      ContDiffOn ℝ 1 (Function.uncurry psi) (univ ×ˢ Ioo s T) ∧
      ContinuousOn (Function.uncurry U) (univ ×ˢ Icc s T) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (fun y => U y z.2) z.1)
        (univ ×ˢ Icc s T) ∧
      ContinuousOn (fun z : ℝ × ℝ => deriv (deriv (fun y => U y z.2)) z.1)
        (univ ×ˢ Icc s T) ∧
      ContDiffOn ℝ 1 (Function.uncurry U) (univ ×ˢ Ioo s T) ∧
      (∀ t ∈ Icc s T, ∀ y,
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (q y t)) (V y t) ≠ 0 ∧
        ⟪V y t, deriv r y⟫ ≠ 0) ∧
      ∀ t ∈ Ioo s T, ∀ y, HasDerivAt (U y)
        (A y t • deriv (deriv (fun z => U z t)) y + Bgraph y t) t := by
  classical
  let Z := Icc s T
  let q0 : Z → ℝ → W := fun t x => e (c x t)
  obtain ⟨hspace, _hpush0, hvalue, hjet, hcurv⟩ :=
    c2ShrinkingCurve_embedded_closed_data hc he
  have hparam : Continuous (fun p : Z × ℝ => (p.2, (p.1 : ℝ))) :=
    continuous_snd.prodMk continuous_fst.subtype_val
  have hq0 : Continuous (fun p : Z × ℝ => q0 p.1 p.2) :=
    hvalue.comp_continuous hparam (fun p => ⟨mem_univ _, p.1.2⟩)
  have hq1 : Continuous (fun p : Z × ℝ => deriv (q0 p.1) p.2) :=
    hjet.comp_continuous hparam (fun p => ⟨mem_univ _, p.1.2⟩)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨phi0, hdata0, _hPhi0, hPsi0, _hPhi1, hPsi1, hU0, hU1⟩ :=
    exists_curveNormalGraph_continuous_family hr hm hM hB hradius heps
      hlower hupper hsecond hsmall hmargin heta htrans hP hrper hq0 hq1
      (fun t => hspace t t.2) (fun t x => congrArg e (hc.periodic t t.2 x))
      (fun t => hclose t t.2) (fun t => hfirst t t.2)
  let phi : ℝ → (ℝ ≃o ℝ) := fun t =>
    if ht : t ∈ Icc s T then phi0 ⟨t, ht⟩ else OrderIso.refl ℝ
  have hphi (t : Z) : phi t = phi0 t := by
    dsimp only [phi]
    rw [dif_pos (show (t : ℝ) ∈ Icc s T from t.2)]
  have hdata := hdata0
  simp_rw [← hphi] at hdata
  let psi : ℝ → ℝ → ℝ := fun y t => (phi t).symm y
  let q : ℝ → ℝ → M := fun y t => c (psi y t) t
  let U : ℝ → ℝ → W := fun y t => e (q y t) - r y
  let V : ℝ → ℝ → W := fun y t => deriv (fun z => e (q z t)) y
  let A : ℝ → ℝ → ℝ := fun y t => ambientCurvePrincipal F ρ t (e (q y t)) (V y t)
  let Bgraph : ℝ → ℝ → W := fun y t => curveGraphLower (A y t)
    (ambientCurveLower F e ρ t (e (q y t)) (V y t))
    (deriv r y) (deriv (deriv r) y) (deriv (deriv (deriv r)) y)
    (U y t) (deriv (fun z => U z t) y)
  let D : Set (ℝ × ℝ) := univ ×ˢ Icc s T
  have hswap : Continuous (fun z : D =>
      ((⟨z.1.2, z.2.2⟩ : Z), z.1.1)) :=
    (continuous_subtype_val.snd.subtype_mk _).prodMk continuous_subtype_val.fst
  have hpsi : ContinuousOn (Function.uncurry psi) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hPsi0.comp hswap).congr (fun z => by
      simp only [psi, Function.uncurry_def, Set.domRestrict_apply, Function.comp_def, ← hphi])
  have hpsi1 : ContinuousOn (fun z : ℝ × ℝ => deriv (fun y => psi y z.2) z.1) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hPsi1.comp hswap).congr (fun z => by
      simp only [psi, Set.domRestrict_apply, Function.comp_def, ← hphi])
  have hU : ContinuousOn (Function.uncurry U) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hU0.comp hswap).congr (fun z => by
      simp only [U, q, q0, psi, Function.uncurry_def, Set.domRestrict_apply,
        Function.comp_def, ← hphi])
  have hUfirst : ContinuousOn (fun z : ℝ × ℝ => deriv (fun y => U y z.2) z.1) D := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (hU1.comp hswap).congr (fun z => by
      simp only [U, q, q0, psi, Set.domRestrict_apply, Function.comp_def, ← hphi])
  have hPhiC2 (t : ℝ) (ht : t ∈ Icc s T) : ContDiff ℝ 2 (phi t : ℝ → ℝ) :=
    (hdata ⟨t, ht⟩).2.1
  have hPsiC2 (t : ℝ) (ht : t ∈ Icc s T) : ContDiff ℝ 2 (fun y => psi y t) :=
    (hdata ⟨t, ht⟩).2.2.1
  have hPhiPos (t : ℝ) (ht : t ∈ Icc s T) (x : ℝ) : 0 < deriv (phi t) x :=
    (hdata ⟨t, ht⟩).2.2.2.2.1 x
  have hPsiPos (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) :
      0 < deriv (fun z => psi z t) y := ((hdata ⟨t, ht⟩).2.2.2.2.2.1 y).2
  have hUC2 (t : ℝ) (ht : t ∈ Icc s T) : ContDiff ℝ 2 (fun y => U y t) :=
    (hdata ⟨t, ht⟩).2.2.2.2.2.2.2.2.1
  have hnormal (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) : ⟪U y t, deriv r y⟫ = 0 :=
    (hdata ⟨t, ht⟩).2.2.2.2.2.2.2.2.2.2.1 y
  have hC1 : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => e (c z.1 z.2))
      (univ ×ˢ Ioo s T) := by
    simpa only [interior_Icc] using (c2ShrinkingCurve_embedded_interior_equation hc he).1
  have hPhiC1 (t x : ℝ) (ht : t ∈ Ioo s T) :
      ContDiffAt ℝ 1 (fun p : ℝ × ℝ => phi p.1 p.2) (t, x) := by
    have hraw : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => e (c z.1 z.2)) (x, t) :=
      hC1.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)
    have hinput : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (p.2, e (c p.2 p.1))) (t, x) :=
      contDiffAt_snd.prodMk (hraw.comp
        (f := fun p : ℝ × ℝ => (p.2, p.1))
        (g := fun p : ℝ × ℝ => e (c p.1 p.2))
        (t, x) (contDiffAt_snd.prodMk contDiffAt_fst))
    have hfoot := (selectedCurveFootpoint_contDiffAt hr hm hM hB hradius heps
      hlower hupper hsecond hsmall hmargin (x, e (c x t))
        (hclose t (Ioo_subset_Icc_self ht) x)).1.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
    have hcomp := hfoot.comp (f := fun p : ℝ × ℝ => (p.2, e (c p.2 p.1)))
      (t, x) hinput
    apply hcomp.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (t, x), p.1 ∈ Ioo s T :=
      continuous_fst.continuousAt (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hnear] with p hp
    exact (hdata ⟨p.1, Ioo_subset_Icc_self hp⟩).1 p.2
  have hpsiC1 : ContDiffOn ℝ 1 (Function.uncurry psi) (univ ×ˢ Ioo s T) := by
    intro z hz
    have ht := Ioo_subset_Icc_self hz.2
    have hinv := contDiffAt_inverse_orderIso_family phi (by norm_num : (1 : ℕ∞ω) ≠ 0)
      (hPhiC1 z.2 (psi z.1 z.2) hz.2)
      ((hPhiC2 z.2 ht).differentiable (by norm_num) (psi z.1 z.2)).hasDerivAt
      (hPhiPos z.2 ht (psi z.1 z.2)).ne'
    exact (hinv.comp (f := fun p : ℝ × ℝ => (p.2, p.1)) z
      (contDiffAt_snd.prodMk contDiffAt_fst)).contDiffWithinAt
  have hUC1 : ContDiffOn ℝ 1 (Function.uncurry U) (univ ×ˢ Ioo s T) :=
    (hC1.comp (s := univ ×ˢ Ioo s T) (hpsiC1.prodMk contDiffOn_snd)
      (fun _ hz => ⟨mem_univ _, hz.2⟩)).sub
      ((hr.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).comp contDiff_fst).contDiffOn
  have hr1 : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hqspace (t : ℝ) (ht : t ∈ Icc s T) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t) :=
    (hc.spatial_regular t ht).comp (hPsiC2 t ht).contMDiff
  have hqimm (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) :
      curveVelocity (n := n) (fun z => q z t) y ≠ 0 := by
    have hv := curveVelocity_comp (phi := fun z => psi z t)
      (((hc.spatial_regular t ht) (psi y t)).mdifferentiableAt (by norm_num))
      ((hPsiC2 t ht).differentiable (by norm_num) y).hasDerivAt
    change curveVelocity (n := n) (fun z => q z t) y = _ at hv
    rw [hv]
    exact smul_ne_zero (hPsiPos t ht y).ne' (hc.immersed t ht (psi y t))
  have hV (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) :
      V y t = deriv r y + deriv (fun z => U z t) y := by
    have hdiff : Differentiable ℝ (fun z => e (q z t)) :=
      ((hspace t ht).comp (hPsiC2 t ht)).differentiable (by norm_num)
    have hd := deriv_sub (hdiff y) (hr.differentiable (by simp) y)
    change deriv (fun z => U z t) y = V y t - deriv r y at hd
    rw [hd]
    abel
  have htransverse (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) :
      ⟪V y t, deriv r y⟫ ≠ 0 := by
    have hd := (((hUC2 t ht).differentiable (by norm_num) y).hasDerivAt.inner ℝ
      (hr1.differentiable (by simp) y).hasDerivAt).unique
        ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (hnormal t ht)))
    have hidentity : ⟪V y t, deriv r y⟫ =
        ‖deriv r y‖ ^ 2 - ⟪U y t, deriv (deriv r) y⟫ := by
      rw [hV t ht y, inner_add_left, real_inner_self_eq_norm_sq]
      linarith only [hd]
    have hw : |y - psi y t| < radius := by
      simpa only [psi, OrderIso.apply_symm_apply] using
        (hdata ⟨t, ht⟩).2.2.2.1 (psi y t)
    have hy : y ∈ Icc (psi y t - radius) (psi y t + radius) :=
      ⟨by linarith [(abs_lt.mp hw).1], by linarith [(abs_lt.mp hw).2]⟩
    have hl := curveFootpoint_denominator_lower hr hm hM hB hradius heps
      hlower hupper hsecond hsmall (hclose t ht (psi y t)) hy
    have hpos : 0 < ⟪V y t, deriv r y⟫ := by
      rw [hidentity]
      exact lt_of_lt_of_le (by positivity) hl
    exact hpos.ne'
  have hprojected (t : ℝ) (ht : t ∈ Icc s T) (y : ℝ) :
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (q y t)) (V y t) ≠ 0 := by
    have hchain : fderiv ℝ (fun z => e (q z t)) y =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q y t)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun z => q z t) y) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp y (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hqspace t ht y).mdifferentiableAt (by norm_num))
    have hpush := congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
    change V y t = mfderiv (𝓡 n) 𝓘(ℝ, W) e (q y t)
      (curveVelocity (n := n) (fun z => q z t) y) at hpush
    rw [hpush]
    erw [(smooth_retraction_differentials he hN heN hρ hret).2.2]
    exact hqimm t ht y
  have hVcont : ContinuousOn (Function.uncurry V) D := by
    have hsum := ((hr1.continuous.comp continuous_fst).continuousOn.add hUfirst)
    exact hsum.congr (fun z hz => hV z.2 hz.2 z.1)
  let eta0 : ℝ × ℝ → W := fun z =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (q z.1 z.2) (m62CurvatureVector F q z.2 z.1)
  have heta0 : ContinuousOn eta0 D := by
    have hcomposed := hcurv.comp (s := D) (hpsi.prodMk continuousOn_snd)
      (fun _ hz => ⟨mem_univ _, hz.2⟩)
    apply hcomposed.congr
    intro z hz
    have hS := unitTangent_contMDiff_of_c2 F c
      (hc.spatial_regular z.2 hz.2) (hc.immersed z.2 hz.2)
    have hcurvature : m62CurvatureVector F q z.2 z.1 =
        m62CurvatureVector F c z.2 (psi z.1 z.2) :=
      curvatureVector_comp F c ((hc.spatial_regular z.2 hz.2).mdifferentiable (by norm_num))
        ((hPsiC2 z.2 hz.2).differentiable (by norm_num)) (hPsiPos z.2 hz.2)
        ((hS (psi z.1 z.2)).mdifferentiableAt (by simp))
    dsimp only [eta0, Function.comp_def]
    rw [hcurvature]
    rfl
  let G := ℝ × (W × W)
  let Ω : Set G := {z | r z.1 + z.2.1 ∈ N ∧
    mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
    ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}
  let J : ℝ × ℝ → ℝ × G := fun z =>
    (z.2, (z.1, (U z.1 z.2, deriv (fun y => U y z.2) z.1)))
  have hJ : ContinuousOn J D :=
    continuousOn_snd.prodMk (continuousOn_fst.prodMk (hU.prodMk hUfirst))
  have hpoint (y t : ℝ) : r y + U y t = e (q y t) := by
    dsimp only [U]
    abel
  have hJmem (z : ℝ × ℝ) (hz : z ∈ D) : J z ∈ Icc a b ×ˢ Ω := by
    refine ⟨hc.domain_subset hz.2, ?_⟩
    change r z.1 + U z.1 z.2 ∈ N ∧ _
    rw [hpoint, ← hV z.2 hz.2 z.1]
    exact ⟨heN (mem_range_self _), hprojected z.2 hz.2 z.1, htransverse z.2 hz.2 z.1⟩
  obtain ⟨hAraw, hBraw, hApos⟩ := curveGraphCoefficients_contDiffOn F he hN hρ hr
  have hAcont : ContinuousOn (Function.uncurry A) D := by
    have hcomp := hAraw.continuousOn.comp hJ hJmem
    exact hcomp.congr (fun z hz => by
      dsimp only [J, Function.comp_def, Function.uncurry_def, A]
      rw [hpoint, ← hV z.2 hz.2 z.1])
  have hBcont : ContinuousOn (Function.uncurry Bgraph) D := by
    have hcomp := hBraw.continuousOn.comp hJ hJmem
    exact hcomp.congr (fun z hz => by
      dsimp only [J, Function.comp_def, Function.uncurry_def, Bgraph, A]
      rw [hpoint, ← hV z.2 hz.2 z.1])
  have hAne (z : ℝ × ℝ) (hz : z ∈ D) : A z.1 z.2 ≠ 0 := by
    have hp := hApos z.2 (J z).2 (hJmem z hz).2
    dsimp only [J] at hp
    rw [hpoint, ← hV z.2 hz.2 z.1] at hp
    exact hp.ne'
  have hUsecond : ContinuousOn
      (fun z : ℝ × ℝ => deriv (deriv (fun y => U y z.2)) z.1) D := by
    apply continuousOn_graph_acceleration hAcont hBcont hVcont
      (hr1.continuous.comp continuous_fst).continuousOn heta0 hAne
      (fun z hz => htransverse z.2 hz.2 z.1)
    intro z hz
    exact normalGraph_curvature_projection F he hN heN hρ hret q
      (hqspace z.2 hz.2) (hqimm z.2 hz.2) hr (hnormal z.2 hz.2) z.1
      (htransverse z.2 hz.2 z.1)
  refine ⟨phi, fun t ht => hdata ⟨t, ht⟩, hpsi, hpsi1, hpsiC1,
    hU, hUfirst, hUsecond, hUC1,
    fun t ht y => ⟨hprojected t ht y, htransverse t ht y⟩, ?_⟩
  intro t ht y
  have htime : DifferentiableAt ℝ (psi y) t :=
    ((hpsiC1.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      ⟨mem_univ y, ht⟩)).differentiableAt (by norm_num)).comp t
        (differentiableAt_const y |>.prodMk differentiableAt_id)
  exact normalGraph_hasDerivAt_time he hN heN hρ hret hc hr psi
    (by simpa only [interior_Icc] using ht) (hPsiC2 t (Ioo_subset_Icc_self ht))
    (hPsiPos t (Ioo_subset_Icc_self ht)) htime hnormal
    (htransverse t (Ioo_subset_Icc_self ht) y)

end PoincareConjecture.M63
