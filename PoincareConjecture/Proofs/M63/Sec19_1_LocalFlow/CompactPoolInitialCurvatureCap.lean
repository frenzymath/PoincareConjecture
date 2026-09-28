import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.InitialCurvatureCap
import Mathlib.Topology.Order.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle L, W)
local notation "J" => ((X × X) × X) × ℝ




theorem exists_compact_pool_initial_curvature_bound
    (F : RicciFlow n M (Icc a b)) {tau : ℝ} (htau : tau ∈ Icc a b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {K : Set J} (hK : IsCompact K)
    (hjets : ∀ p ∈ K, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => p.1.1.1 (y : AddCircle L))
        (p.1.1.2 (x : AddCircle L)) x ∧
      HasDerivAt (fun y : ℝ => p.1.1.2 (y : AddCircle L))
        (p.1.2 (x : AddCircle L)) x)
    (hguard : ∀ p ∈ K, ∀ x : ℝ,
      p.1.1.1 (x : AddCircle L) ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (p.1.1.1 (x : AddCircle L))
        (p.1.1.2 (x : AddCircle L)) ≠ 0)
    (hfixed : ∀ p ∈ K, ∀ x : ℝ,
      p.1.1.1 (x : AddCircle L) = e (ρ (p.1.1.1 (x : AddCircle L)))) :
    ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ p ∈ K, ∀ κ : ℝ, 0 < κ → ∀ x : ℝ,
      m62CurvatureSquared F
        (fun y (_ : ℝ) => ρ (p.1.1.1 ((κ * y : ℝ) : AddCircle L))) tau x ≤ R0 := by
  classical
  let f : J → ℝ → W := fun p x => p.1.1.1 (x : AddCircle L)
  let f1 : J → ℝ → W := fun p x => p.1.1.2 (x : AddCircle L)
  let f2 : J → ℝ → W := fun p x => p.1.2 (x : AddCircle L)
  have hder (p : J) (hp : p ∈ K) : deriv (f p) = f1 p :=
    funext fun x => (hjets p hp x).1.deriv
  have hder2 (p : J) (hp : p ∈ K) : deriv (deriv (f p)) = f2 p := by
    rw [hder p hp]
    exact funext fun x => (hjets p hp x).2.deriv
  have hf1 (p : J) (hp : p ∈ K) : ContDiff ℝ 1 (f1 p) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    exact ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (f2 p x),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).continuous.comp
        (p.1.2.continuous.comp (AddCircle.continuous_mk' L)),
      fun x => (hjets p hp x).2.hasFDerivAt⟩
  have hf (p : J) (hp : p ∈ K) : ContDiff ℝ 2 (f p) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    exact ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (f1 p x),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).contDiff.comp (hf1 p hp),
      fun x => (hjets p hp x).1.hasFDerivAt⟩
  have hfguard (p : J) (hp : p ∈ K) (x : ℝ) :
      f p x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f p x) (deriv (f p) x) ≠ 0 := by
    rw [hder p hp]
    exact hguard p hp x
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let α := fun z : W × W => ambientCurvePrincipal F ρ tau z.1 z.2
  let β := fun z : W × W => ambientCurveLower F e ρ tau z.1 z.2
  let lam : W × W → W →L[ℝ] ℝ := fun z => (1 / 2 : ℝ) •
    (fderiv ℝ α z).comp (ContinuousLinearMap.inr ℝ W W)
  let η := fun z : W × W => fderiv ℝ α z (z.2, 0) / 2
  let C : W × W → W →L[ℝ] W :=
    fun z => α z • ContinuousLinearMap.id ℝ W + (lam z).smulRight z.2
  let d : W × W → W := fun z => β z + η z • z.2
  obtain ⟨_hLam, _hη, hC, hd, hformula⟩ :=
    ambientCurve_curvature_label_affine F he hU heU hρ hρe htau
  let D : Set ((W × W) × W) := {z | z.1 ∈ Ω}
  let P : (W × W) × W → W := fun z => C z.1 z.2 + d z.1
  let k : (W × W) × W → ℝ := fun z => (F.metric tau).inner (ρ z.1.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.1 (P z))
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.1 (P z))
  have hP : ContinuousOn P D :=
    ((hC.comp continuous_fst.continuousOn (fun _ hz => hz)).clm_apply
      continuousOn_snd).add (hd.comp continuous_fst.continuousOn (fun _ hz => hz))
  have hk : ContinuousOn k D := by
    have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
      (f := fun _ => 0) contMDiff_const).1.continuousOn
    exact hmetric.comp
      ((continuousOn_const.prodMk continuousOn_fst.fst).prodMk hP)
      (fun z hz => ⟨⟨htau, hz.1⟩, mem_univ _⟩)
  let eval : J × AddCircle L → (W × W) × W :=
    fun z => ((z.1.1.1.1 z.2, z.1.1.1.2 z.2), z.1.1.2 z.2)
  have heval : Continuous eval :=
    ((continuous_fst.fst.fst.fst.eval continuous_snd).prodMk
      (continuous_fst.fst.fst.snd.eval continuous_snd)).prodMk
      (continuous_fst.fst.snd.eval continuous_snd)
  let compactJets : Set ((W × W) × W) := eval '' (K ×ˢ univ)
  have hcompact : IsCompact compactJets := (hK.prod isCompact_univ).image heval
  have hsub : compactJets ⊆ D := by
    rintro z ⟨⟨p, q⟩, hp, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact hguard p hp.1 x
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image (hk.mono hsub)
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hgeom (p : J) (hp : p ∈ K) (x : ℝ) :
      k ((f p x, deriv (f p) x), deriv (deriv (f p)) x) =
        m62CurvatureSquared F (fun y (_ : ℝ) => ρ (f p y)) tau x := by
    have hcurv := (hformula (f p) (hf p hp) (hfguard p hp) (hfixed p hp) x).2
    have hreturn : mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f p x)
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f p x))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f p y)) tau x)) =
        m62CurvatureVector F (fun y (_ : ℝ) => ρ (f p y)) tau x := by
      let dρ : W → W →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        fun z => mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z
      have heq : dρ (f p x) = dρ (e (ρ (f p x))) := congrArg dρ (hfixed p hp x)
      change dρ (f p x)
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (ρ (f p x))
          (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f p y)) tau x)) = _
      rw [heq]
      exact hleft (ρ (f p x))
        (m62CurvatureVector F (fun y (_ : ℝ) => ρ (f p y)) tau x)
    change (F.metric tau).inner (ρ (f p x))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f p x)
        (C (f p x, deriv (f p) x) (deriv (deriv (f p)) x) + d (f p x, deriv (f p) x)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f p x)
        (C (f p x, deriv (f p) x) (deriv (deriv (f p)) x) + d (f p x, deriv (f p) x))) = _
    rw [← hcurv, hreturn]
    rfl
  have hbound (p : J) (hp : p ∈ K) (x : ℝ) :
      m62CurvatureSquared F (fun y (_ : ℝ) => ρ (f p y)) tau x ≤ max 1 B := by
    have hmem : ((f p x, deriv (f p) x), deriv (deriv (f p)) x) ∈ compactJets := by
      rw [hder2 p hp, hder p hp]
      exact mem_image_of_mem eval
        (show (p, (x : AddCircle L)) ∈ K ×ˢ univ from ⟨hp, mem_univ _⟩)
    calc
      _ = k ((f p x, deriv (f p) x), deriv (deriv (f p)) x) := (hgeom p hp x).symm
      _ ≤ B := hB (mem_image_of_mem k hmem)
      _ ≤ max 1 B := le_max_right _ _
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro p hp κ hκ x
  let c := fun y (_ : ℝ) => ρ (f p y)
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y tau) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hf p hp).contMDiff (fun y => (hfguard p hp y).1)
  have hvel (y : ℝ) : curveVelocity (n := n) (fun z => c z tau) y =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f p y) (deriv (f p) y) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ f p) y) 1 = _
    erw [mfderiv_comp y
      ((hρ.contMDiffAt (hU.mem_nhds (hfguard p hp y).1)).mdifferentiableAt (by simp))
      (((hf p hp).contMDiff y).mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have himm (y : ℝ) : curveVelocity (n := n) (fun z => c z tau) y ≠ 0 := by
    rw [hvel]
    exact (hfguard p hp y).2
  have hS := unitTangent_contMDiff_of_c2 F c (t := tau) hc himm
  have hlin (y : ℝ) : HasDerivAt (fun z : ℝ => κ * z) κ y := by
    simpa +instances only [id_eq, mul_one] using! (hasDerivAt_id y).const_mul κ
  change m62CurvatureSquared F (fun y s => c (κ * y) s) tau x ≤ max 1 B
  rw [curvatureSquared_comp F c (hc.mdifferentiable (by norm_num))
    (fun y => (hlin y).differentiableAt) (fun y => by rw [(hlin y).deriv]; exact hκ)
    ((hS (κ * x)).mdifferentiableAt (by norm_num))]
  exact hbound p hp (κ * x)

end PoincareConjecture.M63
