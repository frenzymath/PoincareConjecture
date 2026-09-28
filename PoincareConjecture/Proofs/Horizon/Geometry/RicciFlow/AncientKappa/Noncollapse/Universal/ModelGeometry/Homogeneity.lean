import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.SphereMotions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

local instance : ChartedSpace RoundCylinderCoordinates RoundCylinderSpace :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere ℝ ℝ

local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)

local instance : IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)

private def lineTranslation (a : ℝ) : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := Equiv.addRight a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

private theorem lineTranslation_mfderiv (a z v : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (lineTranslation a) z v = v := by
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => x + a) z v = v
  rw [mfderiv_eq_fderiv]
  simp
  rfl

private theorem productMotion_inner
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (a : ℝ) (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    let d := (Poincare.Geometry.Riemannian.SpaceForm.sphereMotion L).prodCongr
      (lineTranslation a)
    EvolvingRoundCylinderMetric 0 (d z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d z w) =
      EvolvingRoundCylinderMetric 0 z v w := by
  dsimp only
  let f := Poincare.Geometry.Riemannian.SpaceForm.sphereMotion L
  have hd := mfderiv_prodMap (p := z)
    (f.contMDiff.mdifferentiable (by simp) z.1)
    ((lineTranslation a).contMDiff.mdifferentiable (by simp) z.2)
  change _ = _ at hd
  change EvolvingRoundCylinderMetric 0 (f z.1, lineTranslation a z.2)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Prod.map f (lineTranslation a)) z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Prod.map f (lineTranslation a)) z w) = _
  rw [hd]
  change EvolvingRoundCylinderMetric 0 (f z.1, lineTranslation a z.2)
    (mfderiv (𝓡 2) (𝓡 2) f z.1 v.1,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (lineTranslation a) z.2 v.2)
    (mfderiv (𝓡 2) (𝓡 2) f z.1 w.1,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (lineTranslation a) z.2 w.2) = _
  rw [lineTranslation_mfderiv, lineTranslation_mfderiv]
  simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one]
  have hs := Poincare.Geometry.Riemannian.SpaceForm.sphereMotion_inner L z.1 v.1 w.1
  exact congrArg (fun t : ℝ => 2 * t + v.2 * w.2) hs

theorem roundCylinder_exists_motion (p q : RoundCylinderSpace) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) RoundCylinderSpace RoundCylinderSpace ∞,
      e p = q ∧ ∀ z v w,
        roundCylinderMetric.inner (e z)
          (mfderiv (𝓡 3) (𝓡 3) e z v) (mfderiv (𝓡 3) (𝓡 3) e z w) =
          roundCylinderMetric.inner z v w := by
  let L := (ℝ ∙ ((p.1 : EuclideanSpace ℝ (Fin 3)) - q.1))ᗮ.reflection
  have hLp : L p.1 = q.1 := Submodule.reflection_sub (by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.1.property.trans q.1.property.symm)
  let d := (Poincare.Geometry.Riemannian.SpaceForm.sphereMotion L).prodCongr
    (lineTranslation (q.2 - p.2))
  let c := roundCylinderModelDiffeomorph
  let e := (c.symm.trans d).trans c
  have hec (z : RoundCylinderSpace) : e (c z) = c (d z) := by simp [e]
  refine ⟨e, ?_, ?_⟩
  · change ((Poincare.Geometry.Riemannian.SpaceForm.sphereMotion L) p.1,
      p.2 + (q.2 - p.2)) = q
    apply Prod.ext
    · exact Subtype.ext hLp
    · dsimp; ring
  · intro z v w
    obtain ⟨z, rfl⟩ := c.surjective z
    let A := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z
    have hA : Function.Surjective A := by
      have hi := mfderiv_comp (c z) (c.contMDiff.mdifferentiable (by simp) _)
        (c.symm.contMDiff.mdifferentiable (by simp) _)
      rw [show (c ∘ c.symm : RoundCylinderSpace → RoundCylinderSpace) = id from
        funext c.apply_symm_apply, mfderiv_id] at hi
      intro u
      refine ⟨mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) c.symm (c z) u, ?_⟩
      have hu := congrArg (fun f => f u) hi
      change u = mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c (c.symm (c z))
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) c.symm (c z) u) at hu
      erw [c.symm_apply_apply] at hu
      exact hu.symm
    obtain ⟨v, rfl⟩ := hA v
    obtain ⟨w, rfl⟩ := hA w
    have hd : ∀ u : RoundCylinderTangent z,
        mfderiv (𝓡 3) (𝓡 3) e (c z) (A u) =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c (d z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d z u) := by
      intro u
      have h := congrArg (fun f => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z u)
        (show e ∘ c = c ∘ d from funext hec)
      rw [mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
        (c.contMDiff.mdifferentiable (by simp) _),
        mfderiv_comp z (c.contMDiff.mdifferentiable (by simp) _)
        (d.contMDiff.mdifferentiable (by simp) _)] at h
      exact h
    change roundCylinderMetric.inner (e (c z))
      (mfderiv (𝓡 3) (𝓡 3) e (c z) (A v))
      (mfderiv (𝓡 3) (𝓡 3) e (c z) (A w)) = _
    erw [hd v, hd w]
    rw [hec]
    exact (roundCylinderMetric_inner (d z) _ _).trans
      ((productMotion_inner L (q.2 - p.2) z v w).trans
        (roundCylinderMetric_inner z v w).symm)

theorem roundCylinder_ball_volume_eq (p q : RoundCylinderSpace) (r : ℝ) :
    roundCylinderMetric.volumeMeasure (roundCylinderMetric.ball p r) =
      roundCylinderMetric.volumeMeasure (roundCylinderMetric.ball q r) := by
  obtain ⟨e, he, hg⟩ := roundCylinder_exists_motion p q
  simpa only [he] using RiemannianMetric.volumeMeasure_ball_diffeomorph
    roundCylinderMetric roundCylinderMetric e (fun z v w => (hg z v w).symm) p r

end PoincareConjecture
