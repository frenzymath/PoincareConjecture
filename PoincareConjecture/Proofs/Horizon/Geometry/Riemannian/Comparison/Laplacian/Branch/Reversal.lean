import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.NoConjugate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.ExponentialRays

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LaplacianComparison

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem manifoldCovDerivAlong_comp_affine
    (g : RiemannianMetric n M) {q : ℝ → M}
    {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q (a * t + b))
    (hV : DifferentiableAt ℝ (chartField q (q (a * t + b)) V) (a * t + b)) :
    manifoldCovDerivAlong g (fun s => q (a * s + b))
      (fun s => V (a * s + b)) 1 t =
      a • manifoldCovDerivAlong g q V 1 (a * t + b) := by
  let c := extChartAt (𝓡 n) (q (a * t + b))
  have hcurve := (contDiffAt_chart_curve hq (mem_extChartAt_source _)).differentiableAt
    (by simp)
  have hparam : HasDerivAt (fun s : ℝ => a * s + b) a t := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id t).const_mul a).add_const b
  have h := covDerivAlong_comp_curve
    (christoffelBilinear (g.pullbackCoefficients c.symm))
    (c := fun s => a * s + b) (t := t) hcurve hV hparam
  unfold manifoldCovDerivAlong
  dsimp only
  change (mfderiv (𝓡 n) (𝓡 n) c (q (a * t + b))).inverse
      (covDerivAlong _ ((c ∘ q) ∘ (fun s => a * s + b))
        ((chartField q (q (a * t + b)) V) ∘ (fun s => a * s + b)) 1 t) = _
  rw [h]
  simp only [covDerivAlong, fderiv_eq_smul_deriv, one_smul, map_smul,
    smul_apply, ← smul_add]
  rfl

theorem manifoldCovDerivAlong_const_smul
    (g : RiemannianMetric n M) (q : ℝ → M)
    (V : (t : ℝ) → TangentSpace (𝓡 n) (q t)) (a t : ℝ) :
    manifoldCovDerivAlong g q (fun s => a • V s) 1 t =
      a • manifoldCovDerivAlong g q V 1 t := by
  unfold manifoldCovDerivAlong covDerivAlong
  simp only [map_smul]
  rw [show (fun s => a • mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q s)
      (V s)) = a • (fun s => mfderiv (𝓡 n) (𝓡 n)
        (extChartAt (𝓡 n) (q t)) (q s) (V s)) from rfl,
    fderiv_const_smul_field]
  simp only [Pi.smul_apply, smul_apply, ← smul_add, map_smul]

theorem manifoldCovDerivAlong_twice_comp_affine
    (g : RiemannianMetric n M) {q : ℝ → M} {I : Set ℝ}
    {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b t : ℝ}
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hV : ∀ s ∈ I, ContDiffAt ℝ ∞ (chartField q (q s) V) s)
    (ht : a * t + b ∈ I) :
    manifoldCovDerivAlong g (fun s => q (a * s + b))
      (manifoldCovDerivAlong g (fun s => q (a * s + b))
        (fun s => V (a * s + b)) 1) 1 t =
      a ^ 2 • manifoldCovDerivAlong g q (manifoldCovDerivAlong g q V 1) 1
        (a * t + b) := by
  have hnear : ∀ᶠ s in 𝓝 t, a * s + b ∈ I :=
    (show ContinuousAt (fun s : ℝ => a * s + b) t by fun_prop).preimage_mem_nhds
      (hI.mem_nhds ht)
  have heq : manifoldCovDerivAlong g (fun s => q (a * s + b))
      (fun s => V (a * s + b)) 1 =ᶠ[𝓝 t]
      (fun s => a • manifoldCovDerivAlong g q V 1 (a * s + b)) := by
    filter_upwards [hnear] with s hs
    exact manifoldCovDerivAlong_comp_affine g (hq.contMDiffAt (hI.mem_nhds hs))
      ((hV _ hs).differentiableAt (by simp))
  rw [g.manifoldCovDerivAlong_congr_field _ heq,
    manifoldCovDerivAlong_const_smul]
  rw [manifoldCovDerivAlong_comp_affine g (hq.contMDiffAt (hI.mem_nhds ht))
    ((contDiffAt_chartField_covDeriv g hI hq hV ht
      (mem_extChartAt_source _)).differentiableAt (by simp)), smul_smul, pow_two]

theorem mfderiv_comp_affine_apply_one {q : ℝ → M} {a b t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q (a * t + b)) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => q (a * s + b)) t 1 =
      a • mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q (a * t + b) 1 := by
  have hp : HasDerivAt (fun s : ℝ => a * s + b) a t := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id t).const_mul a).add_const b
  have hd := congrArg (fun L => L (1 : ℝ))
    (mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 n) t
      (hq.mdifferentiableAt (by simp)) hp.differentiableAt.mdifferentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (q ∘ (fun s => a * s + b)) t 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q (a * t + b)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => a * s + b) t 1) at hd
  have hp' : fderiv ℝ (fun s : ℝ => a * s + b) t 1 = a := by
    rw [fderiv_eq_smul_deriv, one_smul, hp.deriv]
  erw [mfderiv_eq_fderiv, hp'] at hd
  exact hd.trans (by simpa only [smul_eq_mul, mul_one] using
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q (a * t + b)).map_smul a (1 : ℝ))

private theorem curvature_neg_velocity (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.curvature x u (-v) (-v) = D.curvature x u v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change D.curvatureTensor x u (-v) w (-v) = D.curvatureTensor x u v w v
  rw [show -v = (-1 : ℝ) • v by simp,
    D.curvatureTensor_smul_second, D.curvatureTensor_smul_last]
  ring

theorem jacobi_ne_zero_of_minimizing_terminal [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {γ : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (γ t)} {a b c C : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hgeo : g.IsGeodesicOn γ I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
    (hJ1 : J 1 = 0) (hDJ1 : manifoldCovDerivAlong g γ J 1 1 ≠ 0)
    (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : g.edist (γ 0) (γ 1) = ENNReal.ofReal C) : J c ≠ 0 := by
  let f : ℝ → ℝ := fun s => -1 * s + 1
  let γr := γ ∘ f
  let Jr : (t : ℝ) → TangentSpace (𝓡 n) (γr t) := fun t => J (f t)
  let Ir := f ⁻¹' I
  have hf : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hIr : IsOpen Ir := hI.preimage hf.continuous
  have hγr : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γr Ir :=
    hγ.comp hf.contMDiff.contMDiffOn (fun _ ht => ht)
  have hsubr : Icc (1 - b) (1 - a) ⊆ Ir := by
    intro t ht
    apply hsub
    dsimp [f]
    constructor <;> linarith [ht.1, ht.2]
  have h01 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t ∈ Icc (0 : ℝ) 1 := by
    dsimp [f]
    constructor <;> linarith [ht.1, ht.2]
  have h01I : Icc (0 : ℝ) 1 ⊆ I :=
    fun t ht => hsub ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hJr : ∀ t ∈ Ir, ContDiffAt ℝ ∞ (chartField γr (γr t) Jr) t := by
    intro t ht
    exact (hJ (f t) ht).comp t hf.contDiffAt
  have hgeor : g.IsGeodesicOn γr Ir := hgeo.comp_affine (-1) 1
  have hjacr : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g γr (manifoldCovDerivAlong g γr Jr 1) 1 t =
        -D.curvature (γr t) (Jr t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γr t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γr t 1) := by
    intro t ht
    have hqt := hγ.contMDiffAt (hI.mem_nhds (h01I (h01 t ht)))
    dsimp only [γr, Jr, Function.comp_def, f]
    rw [manifoldCovDerivAlong_twice_comp_affine g hI hγ hJ (h01I (h01 t ht))]
    norm_num only [neg_one_sq, one_smul]
    rw [hjac _ (h01 t ht), mfderiv_comp_affine_apply_one hqt]
    simp only [neg_smul, one_smul, curvature_neg_velocity]
    rfl
  have hJr0 : Jr 0 = 0 := by
    change (J (-1 * 0 + 1) : EuclideanSpace ℝ (Fin n)) = 0
    rw [show (-1 : ℝ) * 0 + 1 = 1 by ring]
    exact hJ1
  have hDJr0 : manifoldCovDerivAlong g γr Jr 1 0 ≠ 0 := by
    have hq := hγ.contMDiffAt (hI.mem_nhds (h01I (show (1 : ℝ) ∈ Icc 0 1 by simp)))
    have hd := manifoldCovDerivAlong_comp_affine g (a := -1) (b := 1) (t := 0)
      (by simpa using hq) (by simpa using (hJ 1 (h01I (by simp))).differentiableAt (by simp))
    dsimp only [γr, Jr, Function.comp_def, f]
    rw [hd]
    change ((-1 : ℝ) • manifoldCovDerivAlong g γ J 1 (-1 * 0 + 1) :
      EuclideanSpace ℝ (Fin n)) ≠ 0
    rw [show (-1 : ℝ) * 0 + 1 = 1 by ring]
    simpa using hDJ1
  have hspeedr : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γr t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γr t 1) = C := by
    intro t ht
    have hqt := hγ.contMDiffAt (hI.mem_nhds (h01I (h01 t ht)))
    dsimp only [γr, Function.comp_def, f]
    rw [mfderiv_comp_affine_apply_one hqt]
    simpa only [neg_smul, one_smul, RiemannianMetric.tangentNorm, map_neg,
      neg_apply, neg_neg] using hspeed (f t) (h01 t ht)
  have hminr : g.edist (γr 0) (γr 1) = ENNReal.ofReal C := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hcomm : g.edist (γ 1) (γ 0) = g.edist (γ 0) (γ 1) :=
      Manifold.riemannianEDist_comm
    simpa [γr, f] using hcomm.trans hmin
  have hn := Conjugate.jacobi_ne_zero_of_minimizing g D
    (a := 1 - b) (b := 1 - a) (c := 1 - c)
    (by linarith) (by linarith) (by constructor <;> linarith [hc.1, hc.2])
    hIr hγr hgeor hsubr hJr hjacr hJr0 hDJr0 hC hspeedr hminr
  change (J (-1 * (1 - c) + 1) : EuclideanSpace ℝ (Fin n)) ≠ 0 at hn
  rw [show -1 * (1 - c) + 1 = c by ring] at hn
  exact hn

end PoincareConjecture.LaplacianComparison
