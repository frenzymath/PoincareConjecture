import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.MovingDensityVariation

/-!
# Spatial regularity of the actual variation velocity

A joint C2 plane variation has a C1 time-velocity field on each spatial
slice. The proof uses the parameter-dependent manifold derivative and
retains the actual tangent-bundle field. Source: Morgan--Tian Lemma 19.2,
p. 438; M65 derivation 24, fifth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in
-- The dependent parameter-derivative field needs extra elaboration budget.
/-- The actual time velocity of a joint C2 variation is a C1 spatial
tangent field. Source: MT Lemma 19.2, p. 438; M65 derivation 24, fifth stage. -/
theorem m65PlaneTimeVelocity_contMDiffAt (u : ℝ → LoopPlane → M)
    {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z)) :
    ContMDiffAt (𝓡 2) ((𝓡 n).prod (𝓡 n)) 1
      (fun w => (⟨u t w, curveVelocity (fun s => u s w) t⟩ : TangentBundle (𝓡 n) M)) z := by
  have hswap : ContMDiffAt ((𝓡 2).prod (𝓘(ℝ, ℝ))) (𝓡 n) 2
      (Function.uncurry (fun w s => u s w)) (z, t) :=
    hu.comp (z, t) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hbase : ContMDiffAt (𝓡 2) (𝓡 n) 1 (u t) z :=
    (hu.of_le (by norm_num)).comp z (contMDiffAt_const.prodMk contMDiffAt_id)
  have hcoord := hswap.mfderiv (fun w s => u s w) (fun _ : LoopPlane => t) (m := 1)
    contMDiffAt_const (by norm_num)
  have hv : ContMDiffAt (𝓡 2) ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) 1
      (fun _ : LoopPlane => (⟨t, (1 : ℝ)⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) z :=
    contMDiffAt_const
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (IB₁ := 𝓘(ℝ, ℝ)) (IB₂ := 𝓡 n) (IM := 𝓡 2)
    (E₁ := TangentSpace (𝓘(ℝ, ℝ))) (E₂ := TangentSpace (𝓡 n))
    (b₁ := fun _ : LoopPlane => t) (b₂ := u t)
    (ϕ := fun w => mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => u s w) t)
    (v := fun _ => (1 : ℝ)) hcoord hv hbase

end PoincareMT
