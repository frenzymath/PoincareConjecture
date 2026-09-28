import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceGaugeCurvatureLp
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingScalars
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

open M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι

theorem m63UniformInitialCurvatureSquared_bound
    (F : RicciFlow n M (Icc a b)) (ha : a ∈ Icc a b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {f : ℝ → W} (hf : ContDiff ℝ 2 f) (hfp : Function.Periodic f L)
    (r : ℕ → ℝ → W) (hr : ∀ j, ContDiff ℝ 2 (r j))
    (hrp : ∀ j, Function.Periodic (r j) L)
    (hfguard : ∀ x, f x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) ≠ 0)
    (hrguard : ∀ j x, r j x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j x) (deriv (r j) x) ≠ 0)
    (hrfixed : ∀ j x, r j x = e (ρ (r j x)))
    (hconv : ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x,
      ‖r j x - f x‖ < eps ∧ ‖deriv (r j) x - deriv f x‖ < eps ∧
        ‖deriv (deriv (r j)) x - deriv (deriv f) x‖ < eps) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ j (κ : ℝ), 0 < κ → ∀ x,
      m62CurvatureSquared F (fun y (_ : ℝ) => ρ (r j (κ * y))) a x ≤ R0 := by
  classical
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
  let P : (W × W) × W → W := fun z => C z.1 z.2 + d z.1
  let K : (W × W) × W → ℝ := fun z => (F.metric a).inner (ρ z.1.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.1 (P z))
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.1 (P z))
  have hP : ContinuousOn P D :=
    ((hC.comp continuous_fst.continuousOn (fun _ hz => hz)).clm_apply
      continuousOn_snd).add (hd.comp continuous_fst.continuousOn (fun _ hz => hz))
  have hK : ContinuousOn K D := by
    have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
      (f := fun _ => 0) contMDiff_const).1.continuousOn
    exact hmetric.comp
      ((continuousOn_const.prodMk continuousOn_fst.fst).prodMk hP)
      (fun z hz => ⟨⟨ha, hz.1⟩, mem_univ _⟩)
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hgeom (j : ℕ) (x : ℝ) :
      K ((r j x, deriv (r j) x), deriv (deriv (r j)) x) =
        m62CurvatureSquared F (fun y (_ : ℝ) => ρ (r j y)) a x := by
    have hcurv := (hformula (r j) (hr j) (hrguard j) (hrfixed j) x).2
    have hreturn : mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j x)
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (r j x))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (r j y)) a x)) =
        m62CurvatureVector F (fun y (_ : ℝ) => ρ (r j y)) a x := by
      let dρ : W → W →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        fun z => mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z
      have heq : dρ (r j x) = dρ (e (ρ (r j x))) := congrArg dρ (hrfixed j x)
      change dρ (r j x)
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (r j x))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (r j y)) a x)) = _
      rw [heq]
      exact hleft (ρ (r j x)) (m62CurvatureVector F (fun y (_ : ℝ) => ρ (r j y)) a x)
    change (F.metric a).inner (ρ (r j x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j x)
        (C (r j x, deriv (r j) x) (deriv (deriv (r j)) x) + d (r j x, deriv (r j) x)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j x)
        (C (r j x, deriv (r j) x) (deriv (deriv (r j)) x) + d (r j x, deriv (r j) x))) = _
    rw [← hcurv, hreturn]
    rfl
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
  let J := fun j => liftJet (r j) (hr j) (hrp j)
  have hJ : Tendsto J atTop (𝓝 J0) := by
    apply Metric.tendsto_atTop.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := hconv (eps / 2) (by positivity)
    refine ⟨N, fun j hj => ?_⟩
    have hnorm : ‖J j - J0‖ ≤ eps / 2 := by
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      change max (max ‖r j x - f x‖ ‖deriv (r j) x - deriv f x‖)
        ‖deriv (deriv (r j)) x - deriv (deriv f) x‖ ≤ eps / 2
      exact max_le (max_le (hN j hj x).1.le (hN j hj x).2.1.le) (hN j hj x).2.2.le
    simpa only [dist_eq_norm] using hnorm.trans_lt (by linarith)
  have hJmem (j : ℕ) (z : AddCircle L) : J j z ∈ D := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact hrguard j x
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
  let KS : C(D, ℝ) := ⟨fun z => K z, continuousOn_iff_continuous_domRestrict.mp hK⟩
  let k := fun j => KS.comp (J' j)
  have hk : Tendsto k atTop (𝓝 (KS.comp J0')) :=
    (KS.continuous_postcomp.tendsto J0').comp hJ'
  obtain ⟨B, hB⟩ := hk.isCompact_insert_range.exists_bound_of_continuousOn
    (continuous_id.continuousOn)
  have hbound (j : ℕ) (x : ℝ) :
      m62CurvatureSquared F (fun y (_ : ℝ) => ρ (r j y)) a x ≤ max 1 B := by
    calc
      _ = k j (x : AddCircle L) := (hgeom j x).symm
      _ ≤ ‖k j‖ := (k j).apply_le_norm _
      _ ≤ B := hB (k j) (mem_insert_of_mem _ (mem_range_self j))
      _ ≤ max 1 B := le_max_right _ _
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro j κ hκ x
  let c := fun y (_ : ℝ) => ρ (r j y)
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y a) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hr j).contMDiff (fun y => (hrguard j y).1)
  have hvel (y : ℝ) : curveVelocity (n := n) (fun z => c z a) y =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r j y) (deriv (r j) y) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ r j) y) 1 = _
    erw [mfderiv_comp y
      ((hρ.contMDiffAt (hU.mem_nhds (hrguard j y).1)).mdifferentiableAt (by simp))
      (((hr j).contMDiff y).mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have himm (y : ℝ) : curveVelocity (n := n) (fun z => c z a) y ≠ 0 := by
    rw [hvel]
    exact (hrguard j y).2
  have hS := unitTangent_contMDiff_of_c2 F c (t := a) hc himm
  have hlin (y : ℝ) : HasDerivAt (fun z : ℝ => κ * z) κ y := by
    simpa +instances only [id_eq, mul_one] using! (hasDerivAt_id y).const_mul κ
  change m62CurvatureSquared F (fun y s => c (κ * y) s) a x ≤ max 1 B
  rw [curvatureSquared_comp F c (hc.mdifferentiable (by norm_num))
    (fun y => (hlin y).differentiableAt) (fun y => by rw [(hlin y).deriv]; exact hκ)
    ((hS (κ * x)).mdifferentiableAt (by norm_num))]
  exact hbound j (κ * x)

end PoincareConjecture
