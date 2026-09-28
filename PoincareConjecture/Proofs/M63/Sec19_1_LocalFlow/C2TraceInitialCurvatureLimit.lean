import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceGaugeCurvatureLp
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingScalars
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι

theorem exists_uniform_initial_embeddedCurvature_limit
    (F : RicciFlow n M (Icc a b)) (ha : a ∈ Icc a b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {f : ℝ → W} (hf : ContDiff ℝ 2 f) (hfp : Function.Periodic f L)
    (fn : ℕ → ℝ → W) (hfn : ∀ j, ContDiff ℝ 2 (fn j))
    (hfnp : ∀ j, Function.Periodic (fn j) L)
    (hfguard : ∀ x, f x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) ≠ 0)
    (hfnguard : ∀ j x, fn j x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (fn j x) (deriv (fn j) x) ≠ 0)
    (hfnfixed : ∀ j x, fn j x = e (ρ (fn j x)))
    (hconv : ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
      ‖fn j x - f x‖ < eps ∧ ‖deriv (fn j) x - deriv f x‖ < eps ∧
        ‖deriv (deriv (fn j)) x - deriv (deriv f) x‖ < eps) :
    let κ := L / curvePeriod
    ∃ (Hn : ℕ → C(AddCircle curvePeriod, W)) (h0 : C(AddCircle curvePeriod, W)),
      Tendsto Hn atTop (𝓝 h0) ∧
      (∀ j (x : ℝ), Hn j (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (fn j (κ * x)))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (fn j (κ * y))) a x)) ∧
      ∀ x : ℝ, h0 (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f (κ * x)))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f (κ * y))) a x) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let κ := L / curvePeriod
  have hκ : 0 < κ := div_pos (Fact.out : 0 < L) (Fact.out : 0 < curvePeriod)
  have hfpoint (x : ℝ) : Tendsto (fun j => fn j x) atTop (𝓝 (f x)) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hconv eps heps
    exact ⟨N, fun j hj => by simpa only [dist_eq_norm] using (hN j hj x).1⟩
  have hffixed (x : ℝ) : f x = e (ρ (f x)) := by
    have hmap : ContinuousAt (fun z : W => e (ρ z)) (f x) :=
      he.continuous.continuousAt.comp
        ((hρ.contMDiffAt (hU.mem_nhds (hfguard x).1)).continuousAt)
    have hpost := hmap.tendsto.comp (hfpoint x)
    have heq : (fun j => e (ρ (fn j x))) = fun j => fn j x :=
      funext fun j => (hfnfixed j x).symm
    rw [Function.comp_def, heq] at hpost
    exact tendsto_nhds_unique (hfpoint x) hpost
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let α := fun z : W × W => ambientCurvePrincipal F ρ a z.1 z.2
  let β := fun z : W × W => ambientCurveLower F e ρ a z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ α z).comp (ContinuousLinearMap.inr ℝ W W)
  let η := fun z : W × W => fderiv ℝ α z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => α z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => β z + η z • z.2
  obtain ⟨_hLam, _hη, hC, hd, hformula⟩ :=
    ambientCurve_curvature_label_affine F he hU heU hρ hρe ha
  let D : Set ((W × W) × W) := {z | z.1 ∈ Ω}
  let Phi : (W × W) × W → W := fun z => C z.1 z.2 + d z.1
  have hPhi : ContinuousOn Phi D :=
    ((hC.comp continuous_fst.continuousOn (fun _ hz => hz)).clm_apply
      continuousOn_snd).add (hd.comp continuous_fst.continuousOn (fun _ hz => hz))
  let liftJet (g : ℝ → W) (hg : ContDiff ℝ 2 g) (hp : Function.Periodic g L) :
      C(AddCircle L, (W × W) × W) := by
    have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv' (n := 1)
    have hp1 := hp.deriv_of_differentiable (hg.differentiable (by norm_num))
    have hp2 := hp1.deriv_of_differentiable (hg1.differentiable (by norm_num))
    have hper : Function.Periodic (fun x => ((g x, deriv g x), deriv (deriv g) x)) L := by
      intro x
      simp only [hp x, hp1 x, hp2 x]
    exact ⟨hper.lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
        ((hg.continuous.prodMk hg1.continuous).prodMk hg1.continuous_deriv_one)⟩
  let J0 := liftJet f hf hfp
  let J := fun j => liftJet (fn j) (hfn j) (hfnp j)
  have hJ : Tendsto J atTop (𝓝 J0) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hconv (eps / 2) (by positivity)
    refine ⟨N, fun j hj => ?_⟩
    have hnorm : ‖J j - J0‖ ≤ eps / 2 := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      change max (max ‖fn j x - f x‖ ‖deriv (fn j) x - deriv f x‖)
        ‖deriv (deriv (fn j)) x - deriv (deriv f) x‖ ≤ eps / 2
      exact max_le (max_le (hN j hj x).1.le (hN j hj x).2.1.le) (hN j hj x).2.2.le
    simpa only [dist_eq_norm] using hnorm.trans_lt (by linarith)
  have hJmem (j : ℕ) (z : AddCircle L) : J j z ∈ D := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hfnguard j x
  have hJ0mem (z : AddCircle L) : J0 z ∈ D := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hfguard x
  let J' (j : ℕ) : C(AddCircle L, D) :=
    ⟨fun z => ⟨J j z, hJmem j z⟩, (J j).continuous.subtype_mk _⟩
  let J0' : C(AddCircle L, D) :=
    ⟨fun z => ⟨J0 z, hJ0mem z⟩, J0.continuous.subtype_mk _⟩
  let inc : C(D, (W × W) × W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hJ' : Tendsto J' atTop (𝓝 J0') := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact hJ
  let PhiD : C(D, W) := ⟨fun z => Phi z, continuousOn_iff_continuous_domRestrict.mp hPhi⟩
  let G := fun j => PhiD.comp (J' j)
  let g0 := PhiD.comp J0'
  have hG : Tendsto G atTop (𝓝 g0) :=
    (PhiD.continuous_postcomp.tendsto J0').comp hJ'
  let scaleH := AddCircle.homeomorphAddCircle curvePeriod L
    (Fact.out : 0 < curvePeriod).ne' (Fact.out : 0 < L).ne'
  let scale : C(AddCircle curvePeriod, AddCircle L) := ⟨scaleH, scaleH.continuous⟩
  have hscale (x : ℝ) : scale (x : AddCircle curvePeriod) = ((κ * x : ℝ) : AddCircle L) := by
    change ((x * (curvePeriod⁻¹ * L) : ℝ) : AddCircle L) = _
    congr 1
    dsimp only [κ]
    ring
  have hgeom (g : ℝ → W) (hg : ContDiff ℝ 2 g)
      (hguard : ∀ x, g x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (g x) (deriv g x) ≠ 0)
      (hfixed : ∀ x, g x = e (ρ (g x))) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (g (κ * x)))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (g (κ * y))) a x) =
        Phi ((g (κ * x), deriv g (κ * x)), deriv (deriv g) (κ * x)) := by
    let c := fun y (_ : ℝ) => ρ (g y)
    have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y a) :=
      (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
        hg.contMDiff (fun y => (hguard y).1)
    have hvel (y : ℝ) : curveVelocity (n := n) (fun z => c z a) y =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (g y) (deriv g y) := by
      change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ g) y) 1 = _
      erw [mfderiv_comp y
        ((hρ.contMDiffAt (hU.mem_nhds (hguard y).1)).mdifferentiableAt (by simp))
        ((hg.contMDiff y).mdifferentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
      rfl
    have himm (y : ℝ) : curveVelocity (n := n) (fun z => c z a) y ≠ 0 := by
      rw [hvel]
      exact (hguard y).2
    have hS := unitTangent_contMDiff_of_c2 F c (t := a) hc himm
    have hlin (y : ℝ) : HasDerivAt (fun z : ℝ => κ * z) κ y := by
      simpa +instances only [id_eq, mul_one] using! (hasDerivAt_id y).const_mul κ
    have hcurv := curvatureVector_comp F c (hc.mdifferentiable (by norm_num))
      (fun y => (hlin y).differentiableAt) (fun y => by rw [(hlin y).deriv]; exact hκ)
      ((hS (κ * x)).mdifferentiableAt (by norm_num)) (x := x)
    change mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (κ * x) a)
        (m62CurvatureVector F (fun y s => c (κ * y) s) a x) = _
    rw [hcurv]
    exact (hformula g hg hguard hfixed (κ * x)).2
  refine ⟨fun j => (G j).comp scale, g0.comp scale,
    (scale.continuous_precomp.tendsto g0).comp hG, ?_, ?_⟩
  · intro j x
    change G j (scale (x : AddCircle curvePeriod)) = _
    rw [hscale]
    exact (hgeom (fn j) (hfn j) (hfnguard j) (hfnfixed j) x).symm
  · intro x
    change g0 (scale (x : AddCircle curvePeriod)) = _
    rw [hscale]
    exact (hgeom f hf hfguard hffixed x).symm

end PoincareConjecture.M63
