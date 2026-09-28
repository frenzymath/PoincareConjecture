import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceGaugeCurvatureLp














set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M64.RampTransport

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι




theorem observed_velocity_reconstruction
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {gamma : ℝ → M} (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) gamma) (x : ℝ) :
    mfderiv 𝓘(ℝ, W) (𝓡 n) rho ((e ∘ gamma) x) (deriv (e ∘ gamma) x) =
      curveVelocity gamma x := by
  have hd := mfderiv_comp_apply (f := gamma) (g := e) x
    (he.mdifferentiable (by simp) _) (hgamma x) 1
  rw [mfderiv_eq_fderiv] at hd
  change deriv (e ∘ gamma) x =
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x) (curveVelocity gamma x) at hd
  rw [hd]
  exact (M63.smooth_retraction_differentials he hU heU hrho hre).2.2 _ _





theorem exists_continuous_curve_jet_densities
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {time : ℝ} (htime : time ∈ Icc a b) :
    let O : Set (W × W × W) :=
      {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2.1 ≠ 0}
    IsOpen O ∧ ∃ speed density : W × W × W → ℝ,
      ContinuousOn speed O ∧ ContinuousOn density O ∧
      ∀ gamma : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma →
        (∀ x, curveVelocity (n := n) gamma x ≠ 0) → ∀ x,
          let jet := ((e ∘ gamma) x, deriv (e ∘ gamma) x,
            deriv (deriv (e ∘ gamma)) x)
          jet ∈ O ∧ speed jet = curveSpeed F (fun y _ => gamma y) time x ∧
            density jet = m62Curvature F (fun y _ => gamma y) time x *
              curveSpeed F (fun y _ => gamma y) time x := by
  let O : Set (W × W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2.1 ≠ 0}
  let Omega : Set (W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2 ≠ 0}
  let alpha := fun z : W × W => M63.ambientCurvePrincipal F rho time z.1 z.2
  let beta := fun z : W × W => M63.ambientCurveLower F e rho time z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ alpha z).comp (ContinuousLinearMap.inr ℝ W W)
  let eta := fun z : W × W => fderiv ℝ alpha z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => alpha z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => beta z + eta z • z.2
  obtain ⟨_hlam, _heta, hC, hd, hformula⟩ :=
    M63.ambientCurve_curvature_label_affine F he hU heU hrho hre htime
  have hO : IsOpen O :=
    (M63.isOpen_ambientCurveJetDomain F hU hrho).preimage
      (continuous_fst.prodMk continuous_snd.fst)
  let push : W × W × W → W := fun z => C (z.1, z.2.1) z.2.2 + d (z.1, z.2.1)
  have hpush : ContinuousOn push O :=
    ((hC.comp (continuousOn_fst.prodMk continuousOn_snd.fst) (fun _ hz => hz)).clm_apply
      continuousOn_snd.snd).add
        (hd.comp (continuousOn_fst.prodMk continuousOn_snd.fst) (fun _ hz => hz))
  let square : W × W × W → ℝ := fun z => (F.metric time).inner (rho z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 (push z))
    (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 (push z))
  let speedSquare : W × W × W → ℝ := fun z => (F.metric time).inner (rho z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) rho z.1 z.2.1)
  have hmetric := (M63.flow_pullback_metric_hessian_contDiffOn F hU hrho
    (f := fun _ => 0) contMDiff_const).1.continuousOn
  have hsquare : ContinuousOn square O := hmetric.comp
    ((continuousOn_const.prodMk continuousOn_fst).prodMk hpush)
    (fun z hz => ⟨⟨htime, hz.1⟩, mem_univ _⟩)
  have hspeedSquare : ContinuousOn speedSquare O := hmetric.comp
    ((continuousOn_const.prodMk continuousOn_fst).prodMk continuousOn_snd.fst)
    (fun z hz => ⟨⟨htime, hz.1⟩, mem_univ _⟩)
  let speed := fun z => Real.sqrt (speedSquare z)
  let density := fun z => Real.sqrt (square z) * speed z
  refine ⟨hO, speed, density, hspeedSquare.sqrt,
    hsquare.sqrt.mul hspeedSquare.sqrt, ?_⟩
  intro gamma hgamma himm
  let f := e ∘ gamma
  have hf : ContDiff ℝ 2 f :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hvel (x : ℝ) : mfderiv 𝓘(ℝ, W) (𝓡 n) rho (f x) (deriv f x) =
      curveVelocity gamma x :=
    observed_velocity_reconstruction he hU heU hrho hre
      (hgamma.mdifferentiable (by norm_num)) x
  have hguard (x : ℝ) : (f x, deriv f x) ∈ Omega :=
    ⟨heU (mem_range_self _), by rw [hvel]; exact himm x⟩
  have hfixed (x : ℝ) : f x = e (rho (f x)) := by
    dsimp only [f, Function.comp_apply]
    rw [hre]
  have hreturn := (M63.smooth_retraction_differentials he hU heU hrho hre).2.2
  have hreconstruct : (fun y (_ : ℝ) => rho (f y)) = fun y _ => gamma y := by
    funext y t
    exact hre (gamma y)
  intro x
  have hcurv := (hformula f hf hguard hfixed x).2
  change mfderiv (𝓡 n) 𝓘(ℝ, W) e (rho (f x))
    (m62CurvatureVector F (fun y (_ : ℝ) => rho (f y)) time x) =
      C (f x, deriv f x) (deriv (deriv f) x) + d (f x, deriv f x) at hcurv
  have hback : mfderiv 𝓘(ℝ, W) (𝓡 n) rho (f x)
      (C (f x, deriv f x) (deriv (deriv f) x) + d (f x, deriv f x)) =
      m62CurvatureVector F (fun y (_ : ℝ) => gamma y) time x := by
    rw [← hcurv, hreconstruct]
    change mfderiv 𝓘(ℝ, W) (𝓡 n) rho (e (gamma x))
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (rho (e (gamma x)))
        (m62CurvatureVector F (fun y (_ : ℝ) => gamma y) time x)) = _
    rw [hre]
    exact hreturn (gamma x) (m62CurvatureVector F (fun y (_ : ℝ) => gamma y) time x)
  have hs : speed (f x, deriv f x, deriv (deriv f) x) =
      curveSpeed F (fun y _ => gamma y) time x := by
    dsimp only [speed, speedSquare]
    rw [hvel]
    change Real.sqrt ((F.metric time).inner (rho (e (gamma x)))
      (curveVelocity gamma x) (curveVelocity gamma x)) = _
    rw [hre]
    rfl
  refine ⟨hguard x, hs, ?_⟩
  dsimp only [density]
  rw [hs]
  congr 1
  congr 1
  dsimp only [square, push]
  rw [hback]
  change (F.metric time).inner (rho (e (gamma x)))
    (m62CurvatureVector F (fun y (_ : ℝ) => gamma y) time x)
    (m62CurvatureVector F (fun y (_ : ℝ) => gamma y) time x) = _
  rw [hre]
  rfl




theorem actual_curve_densities_continuous
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho U) (hre : ∀ p, rho (e p) = p)
    {time : ℝ} (htime : time ∈ Icc a b)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    Continuous (curveSpeed F (fun y _ => gamma y) time) ∧
      Continuous (fun x => m62Curvature F (fun y _ => gamma y) time x *
        curveSpeed F (fun y _ => gamma y) time x) := by
  obtain ⟨_hO, speed, density, hspeed, hdensity, hactual⟩ :=
    exists_continuous_curve_jet_densities F he hU heU hrho hre htime
  have hf : ContDiff ℝ 2 (e ∘ gamma) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hgamma).contDiff
  have hf1 : ContDiff ℝ 1 (deriv (e ∘ gamma)) := hf.deriv' (n := 1)
  have hjet : Continuous (fun x => ((e ∘ gamma) x, deriv (e ∘ gamma) x,
      deriv (deriv (e ∘ gamma)) x)) :=
    hf.continuous.prodMk (hf1.continuous.prodMk hf1.continuous_deriv_one)
  refine ⟨?_, ?_⟩
  · exact (hspeed.comp_continuous hjet (fun x => (hactual gamma hgamma himm x).1)).congr
      (fun x => (hactual gamma hgamma himm x).2.1)
  · exact (hdensity.comp_continuous hjet (fun x => (hactual gamma hgamma himm x).1)).congr
      (fun x => (hactual gamma hgamma himm x).2.2)

end PoincareConjecture.M64.RampTransport
