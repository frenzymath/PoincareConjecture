import PoincareConjecture.Proofs.M36.NeckMetricBound
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle
import PoincareConjecture.Definitions.M60MinimalSpheres
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace PoincareConjecture

local instance (p : UnitTwoSphere) : NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (NormedAddCommGroup LoopPlane)

local instance (p : UnitTwoSphere) : InnerProductSpace ℝ (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (InnerProductSpace ℝ LoopPlane)

theorem m60RoundSphereInner_eq_inner (p : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) p) : m60RoundSphereInner p v w = inner ℝ v w :=
  M36.sphere_inclusion_inner p v w

theorem m60Sphere_continuousRiemannianBundle :
    IsContinuousRiemannianBundle LoopPlane (TangentSpace (𝓡 2) : UnitTwoSphere → Type) := by
  let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
  have hinc : Continuous (fun v : TangentBundle (𝓡 2) UnitTwoSphere =>
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1) v.proj v.2 : LoopAmbient)) := by
    exact continuous_snd.comp
      ((tangentBundleModelSpaceHomeomorph (𝓡 3)).continuous.comp
        ((contMDiff_coe_sphere (n := 2) (m := 1)).continuous_tangentMap le_rfl))
  refine ⟨⟨fun _ => innerSL ℝ, ?_, fun _ _ _ => rfl⟩⟩
  rw [continuous_iff_continuousAt]
  intro p
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  rw [continuousAt_clm_apply]
  intro v
  rw [continuousAt_clm_apply]
  intro w
  let e := trivializationAt LoopPlane (TangentSpace (𝓡 2) : UnitTwoSphere → Type) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hsection (a : LoopPlane) : ContinuousAt
      (fun q : UnitTwoSphere => (⟨q, e.symm q a⟩ : TangentBundle (𝓡 2) UnitTwoSphere)) p :=
    (e.continuousOn_symm.continuousAt
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hp, mem_univ a⟩)).comp
      (continuousAt_id.prodMk continuousAt_const)
  have hpair := (hinc.continuousAt.comp (hsection v)).inner (𝕜 := ℝ)
    (hinc.continuousAt.comp (hsection w))
  apply hpair.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  rw [inCoordinates_apply_eq₂ hq hq (mem_univ q)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  change inner ℝ (E := LoopPlane) (e.symm q v) (e.symm q w) = _
  exact (M36.sphere_inclusion_inner q (e.symm q v) (e.symm q w)).symm

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereDifferential_bound (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p),
      g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v) (mfderiv (𝓡 2) (𝓡 n) f p v) ≤
        C * m60RoundSphereInner p v v := by
  let : IsContinuousRiemannianBundle LoopPlane
      (TangentSpace (𝓡 2) : UnitTwoSphere → Type) := m60Sphere_continuousRiemannianBundle
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let Q : Set (TangentBundle (𝓡 2) UnitTwoSphere) :=
    {v | v.proj ∈ (univ : Set UnitTwoSphere) ∧ ‖v.2‖ ≤ 1}
  have hQ : IsCompact Q := Proofs.M58.isCompact_bundle_norm_le isCompact_univ 1
  have hcontinuous : Continuous (fun v : TangentBundle (𝓡 2) UnitTwoSphere =>
      g.inner (f v.proj) (mfderiv (𝓡 2) (𝓡 n) f v.proj v.2)
        (mfderiv (𝓡 2) (𝓡 n) f v.proj v.2)) :=
    (hf.continuous_tangentMap le_rfl).inner_bundle (hf.continuous_tangentMap le_rfl)
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hcontinuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p v
  rw [m60RoundSphereInner_eq_inner, real_inner_self_eq_norm_sq]
  by_cases hv : v = 0
  · subst v
    simp
  · let w : TangentSpace (𝓡 2) p := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := norm_smul_inv_norm hv
    have hmem : (⟨p, w⟩ : TangentBundle (𝓡 2) UnitTwoSphere) ∈ Q :=
      ⟨mem_univ _, hw.le⟩
    have hbound : g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p w)
        (mfderiv (𝓡 2) (𝓡 n) f p w) ≤ max C 0 :=
      (le_abs_self _).trans ((hC _ hmem).trans (le_max_left _ _))
    have heq : g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p v)
        (mfderiv (𝓡 2) (𝓡 n) f p v) =
        ‖v‖ ^ 2 * g.inner (f p) (mfderiv (𝓡 2) (𝓡 n) f p w)
          (mfderiv (𝓡 2) (𝓡 n) f p w) := by
      have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [w, map_smul, smul_apply, smul_eq_mul]
      field_simp
    rw [heq, mul_comm (max C 0)]
    exact mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

end PoincareConjecture

end
