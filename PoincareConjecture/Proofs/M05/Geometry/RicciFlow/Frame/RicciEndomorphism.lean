
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Connection.BoundaryRegularity
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.RicciTransport
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

noncomputable section

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

private lemma contDiffWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {J : Set ℝ} {t : ℝ}
    (hf : ∀ v, ContDiffWithinAt ℝ ∞ (fun s => f s v) J t) :
    ContDiffWithinAt ℝ ∞ f J t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp_contDiffWithinAt t
    (contDiffWithinAt_pi.mpr fun i => hf _)


theorem contDiffOn_metricBilin (F : RicciFlow n M (Ico a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    ContDiffOn ℝ ∞ (fun t => (F.metric t).inner x) (Ico a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro t ht
  exact contDiffWithinAt_clm_of_apply fun v => contDiffWithinAt_clm_of_apply fun w =>
    F.contDiffWithinAt_inner_time ht x v w


def ricciBilin (F : RicciFlow n M (Ico a b)) (x : M) (t : ℝ) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  ricciForm F x t


theorem metricBilin_hasDerivWithinAt (F : RicciFlow n M (Ico a b)) (x : M)
    {t : ℝ} (ht : t ∈ Ico a b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    HasDerivWithinAt (fun s => (F.metric s).inner x)
      ((-2 : ℝ) • ricciBilin F x t) (Ico a b) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  have hd := ((contDiffOn_metricBilin F x t ht).differentiableWithinAt
    (by simp)).hasDerivWithinAt
  simpa only [ricciBilin, ricciForm, smul_smul, show (-2 : ℝ) * -(1 / 2) = 1 by norm_num,
    one_smul] using hd


theorem ricciBilin_apply (F : RicciFlow n M (Ico a b)) (x : M)
    {t : ℝ} (ht : t ∈ Ico a b) (v w : TangentSpace (𝓡 n) x) :
    ricciBilin F x t v w = (F.connection t).ricci x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  have hd := ((metricBilin_hasDerivWithinAt F x ht).clm_apply
    (hasDerivWithinAt_const t (Ico a b) v)).clm_apply
      (hasDerivWithinAt_const t (Ico a b) w)
  have heq := (uniqueDiffOn_Ico a b t ht).eq_deriv (Ico a b) hd (F.equation t ht x v w)
  simp only [smul_apply, map_zero, smul_eq_mul, add_zero] at heq
  linarith

theorem ricciBilin_symm (F : RicciFlow n M (Ico a b)) (x : M)
    {t : ℝ} (ht : t ∈ Ico a b) (v w : TangentSpace (𝓡 n) x) :
    ricciBilin F x t v w = ricciBilin F x t w v := by
  have heq := (uniqueDiffOn_Ico a b t ht).eq_deriv (Ico a b) (F.equation t ht x v w)
    (by simpa only [(F.metric _).symm] using F.equation t ht x w v)
  rw [ricciBilin_apply F x ht, ricciBilin_apply F x ht]
  linarith

theorem metric_ricciEndomorphism_left (F : RicciFlow n M (Ico a b)) (x : M)
    (t : ℝ) (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x (ricciEndomorphism F x t v) w = ricciBilin F x t v w := by
  exact congrArg (fun f : TangentSpace (𝓡 n) x →L[ℝ] ℝ => f w)
    (((F.metric t).inner_isInvertible x).self_apply_inverse (ricciBilin F x t v))

theorem metric_ricciEndomorphism_right (F : RicciFlow n M (Ico a b)) (x : M)
    {t : ℝ} (ht : t ∈ Ico a b) (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x v (ricciEndomorphism F x t w) = ricciBilin F x t v w := by
  rw [(F.metric t).symm, metric_ricciEndomorphism_left, ricciBilin_symm F x ht]


theorem contDiffOn_ricciBilin (F : RicciFlow n M (Ico a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    ContDiffOn ℝ ∞ (ricciBilin F x) (Ico a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  exact ((contDiffOn_metricBilin F x).derivWithin (uniqueDiffOn_Ico a b) (by simp)).const_smul _


theorem contDiffOn_ricciEndomorphism (F : RicciFlow n M (Ico a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    letI : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
    letI : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
    ContDiffOn ℝ ∞ (ricciEndomorphism F x) (Ico a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  intro t ht
  have hi := ((F.metric t).inner_isInvertible x).contDiffAt_map_inverse.comp_contDiffWithinAt t
    (contDiffOn_metricBilin F x t ht)
  exact hi.clm_comp (contDiffOn_ricciBilin F x t ht)

end PoincareConjecture.RicciFlow.Frame
