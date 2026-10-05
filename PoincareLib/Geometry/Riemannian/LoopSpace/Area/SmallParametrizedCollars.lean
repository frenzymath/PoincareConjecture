import PoincareLib.Geometry.Riemannian.LoopSpace.Area.ControlledContraction
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.ParametrizedCollarGluing
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Collar.Area

/-!
# Uniform small-area collars for disks with a C1 boundary parameter

Morgan-Tian Definition 18.17, printed p. 430. Uniformly close C1 loops
with bounded total length can be joined with arbitrarily small area.
The supplied disk must have exactly the inner loop's given boundary
parameter. Regularizing arbitrary boundary homeomorphisms remains a
separate obligation for the full filling infimum.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT

open Proofs.M58

/-- A single metric threshold controls the added area for every close
pair with bounded total length and every disk with the exact inner
parameter. Source: MT Definition 18.17, p. 430, small collar derivation. -/
theorem m60_exists_small_parametrized_collar
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    {Lambda epsilon : ℝ} (hLambda : 0 ≤ Lambda) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ γ₀ γ₁ : C1FreeLoopSpace (M := M),
      (∀ z : LoopCircle, g.edist (γ₁ z) (γ₀ z) < ENNReal.ofReal delta) →
      freeLoopLength g γ₁ + freeLoopLength g γ₀ ≤ Lambda →
      ∀ D : LipschitzSpanningDisk g γ₀, (∀ z : LoopCircle, D.map z = γ₀ z) →
        ∃ D' : LipschitzSpanningDisk g γ₁,
          (∀ z : LoopCircle, D'.map z = γ₁ z) ∧ D'.area < D.area + epsilon := by
  obtain ⟨C, U, B, _, _, hB, h0, h1, _, hC, hp, hq, hsmall⟩ :=
    m60_exists_controlled_local_contraction g hcompact
  obtain ⟨H, hH, hprofile⟩ := exists_diskTimeProfile_derivative_bound
  have hcoef : 0 ≤ H * B * Lambda := mul_nonneg (mul_nonneg hH hB) hLambda
  have hden : 0 < H * B * Lambda + 1 := by linarith
  let A := epsilon / (H * B * Lambda + 1)
  have hA : 0 < A := div_pos hepsilon hden
  have hcost : H * A * B * Lambda < epsilon := by
    have heq : A * (H * B * Lambda + 1) = epsilon := div_mul_cancel₀ _ hden.ne'
    nlinarith [heq]
  obtain ⟨delta, hdelta, hdeltaC⟩ := hsmall A hA
  refine ⟨delta, hdelta, ?_⟩
  intro γ₀ γ₁ hclose hlength D hD
  have hpair (z : LoopCircle) := (hdeltaC (γ₁ z) (γ₀ z) (hclose z)).1
  have hregular : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C (s, γ₁ z, γ₀ z) :=
    fun s hs z => hC (s, γ₁ z, γ₀ z) ⟨hs, hpair z⟩
  have hpclose (t : ℝ) : g.edist (periodicFreeLoop γ₁ t) (periodicFreeLoop γ₀ t) <
      ENNReal.ofReal delta := by
    let z : LoopCircle := ⟨angularPoint t, norm_angularPoint t⟩
    have heq (γ : C1FreeLoopSpace (M := M)) : periodicFreeLoop γ t = γ z := γ.boundary z
    rw [heq γ₁, heq γ₀]
    exact hclose z
  have hpU (t : ℝ) := (hdeltaC _ _ (hpclose t)).1
  have harea := m60LoopCollar_area_le g C γ₀ γ₁ hregular hA.le hB hH
    (fun s hs t => ((hdeltaC _ _ (hpclose t)).2 s hs).le)
    (fun s hs t v => hp (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) ⟨hs, hpU t⟩ v)
    (fun s hs t v => hq (s, periodicFreeLoop γ₁ t, periodicFreeLoop γ₀ t) ⟨hs, hpU t⟩ v)
    hprofile
  obtain ⟨D', hD', hsum⟩ := m60Disk_attach_loopCollar g D hD C h0
    (fun z => h1 (γ₁ z, γ₀ z) (hpair z)) hregular
  refine ⟨D', hD', ?_⟩
  rw [hsum]
  have harea' := harea.trans
    (mul_le_mul_of_nonneg_left hlength (mul_nonneg (mul_nonneg hH hA.le) hB))
  linarith

end PoincareMT
