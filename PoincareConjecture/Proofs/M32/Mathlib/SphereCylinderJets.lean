import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace PoincareConjecture.M32

private theorem contDiff_spatial_iteratedFDeriv
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E × F → G} (hf : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ContDiff 𝕜 ∞ (fun z : E × F => iteratedFDeriv 𝕜 m (fun y => f (z.1, y)) z.2) := by
  induction m with
  | zero =>
    let e := (continuousMultilinearCurryFin0 𝕜 F G).symm.toContinuousLinearEquiv
    exact e.toContinuousLinearMap.contDiff.comp hf
  | succ m ih =>
    let e := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => F) G).symm
    have h : ContDiff 𝕜 ∞ (fun p : E × F =>
        fderiv 𝕜 (fun y : F => iteratedFDeriv 𝕜 m (fun w => f (p.1, w)) y) p.2) :=
      (ih.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv
      (f := fun (p : E × F) (y : F) => iteratedFDeriv 𝕜 m (fun w => f (p.1, w)) y)
      (g := fun p : E × F => p.2) contDiff_snd (by simp)
    convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp h using 1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem contDiff_stereoInvCylinder_joint :
    ContDiff ℝ ∞ (fun z : E × (E × ℝ) => (stereoInvFunAux z.1 z.2.1, z.2.2)) := by
  have hn : ContDiff ℝ ∞ (fun z : E × (E × ℝ) => ‖z.2.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd.fst
  have hs : ContDiff ℝ ∞ (fun z : E × (E × ℝ) => stereoInvFunAux z.1 z.2.1) :=
    ((hn.add contDiff_const).inv (fun z => by positivity)).smul
      ((contDiff_const.smul contDiff_snd.fst).add ((hn.sub contDiff_const).smul contDiff_fst))
  exact hs.prodMk contDiff_snd.snd

private theorem stereoInvCylinder_uniform_spatial_jet_bound [FiniteDimensional ℝ E]
    (R S : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : E) (z : E × ℝ),
      ‖v‖ ≤ 1 → ‖z.1‖ ≤ R → z.2 ∈ Icc (-S) S →
      ‖iteratedFDeriv ℝ m (fun y : E × ℝ => (stereoInvFunAux v y.1, y.2)) z‖ ≤ C := by
  have hc := contDiff_spatial_iteratedFDeriv (contDiff_stereoInvCylinder_joint (E := E)) m
  have hcompact := (isCompact_closedBall (0 : E) 1).prod
    ((isCompact_closedBall (0 : E) R).prod (isCompact_Icc (a := -S) (b := S)))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hc.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro v z hv hz hs
  apply (hC (v, z) ?_).trans (le_max_left _ _)
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hv,
    by simpa only [mem_closedBall, dist_zero_right] using hz, hs⟩

theorem sphereCylinder_chart_symm_uniform_jet_bound [FiniteDimensional ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (R S : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : sphere (0 : E) 1,
      ∀ x : EuclideanSpace ℝ (Fin n) × ℝ,
        ‖x.1‖ ≤ R → x.2 ∈ Icc (-S) S →
        ‖iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) × ℝ =>
          (((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y.1 : E), y.2)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := stereoInvCylinder_uniform_spatial_jet_bound (E := E) R S m
  refine ⟨C, hC, ?_⟩
  intro q x hx hs
  let v : sphere (0 : E) 1 := -q
  let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
  let L : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] E :=
    (ℝ ∙ (v : E))ᗮ.subtypeₗᵢ.comp U.symm.toLinearIsometry
  let A : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (E × ℝ) :=
    L.toContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have heq : (fun y : EuclideanSpace ℝ (Fin n) × ℝ =>
      (((chartAt (EuclideanSpace ℝ (Fin n)) q).symm y.1 : E), y.2)) =
      (fun y : E × ℝ => (stereoInvFunAux (v : E) y.1, y.2)) ∘ A := by
    funext y
    apply Prod.ext _ rfl
    change ((stereographic' n v).symm y.1 : E) = stereoInvFunAux (v : E) (L y.1)
    simpa [stereoInvFunAux, smul_add, L, U] using stereographic'_symm_apply v y.1
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖(L y.1, y.2)‖ ≤ 1 * ‖y‖
    simp only [Prod.norm_def, L.norm_map, one_mul, le_refl]
  have hreg : ContDiff ℝ ∞ (fun y : E × ℝ => (stereoInvFunAux (v : E) y.1, y.2)) :=
    contDiff_stereoInvCylinder_joint.comp (contDiff_const.prodMk contDiff_id)
  rw [heq, A.iteratedFDeriv_comp_right hreg x (by exact_mod_cast le_top)]
  have hcomp :
      ‖(iteratedFDeriv ℝ m (fun y : E × ℝ => (stereoInvFunAux (v : E) y.1, y.2))
        (A x)).compContinuousLinearMap (fun _ : Fin m => A)‖ ≤
      ‖iteratedFDeriv ℝ m (fun y : E × ℝ => (stereoInvFunAux (v : E) y.1, y.2))
        (A x)‖ * ‖A‖ ^ m := by
    simpa using (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m (fun y : E × ℝ => (stereoInvFunAux (v : E) y.1, y.2))
        (A x)) (fun _ : Fin m => A))
  apply hcomp.trans
  have hbase := hb (v : E) (A x) (norm_eq_of_mem_sphere v).le
    ((L.norm_map x.1).trans_le hx) hs
  exact (mul_le_mul hbase (pow_le_pow_left₀ (norm_nonneg A) hA m)
    (pow_nonneg (norm_nonneg A) _) hC).trans_eq (by rw [one_pow, mul_one])

end PoincareConjecture.M32
