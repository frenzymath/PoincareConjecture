import PoincareLib.Geometry.Riemannian.LoopSpace.Area.DiskExtension
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.DiskLipschitz

/-!
# Actual Lipschitz fillings of sufficiently short loops

This assembles the regular disk construction and checks every field of the
spanning-disk convention in Morgan--Tian Definition 18.17, printed p. 430.
The uniform small-area estimate required by Corollary 18.28, p. 434, remains
a separate theorem. See the task's disk-extension derivation.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A global C1 disk extension is an admissible Lipschitz spanning disk,
with identity boundary reparameterization. Source: MT Definition 18.17,
p. 430, used by Corollary 18.28, p. 434. -/
noncomputable def spanningDiskOfC1 (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (F : LoopPlane → M)
    (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) (hboundary : ∀ z : LoopCircle, F z.val = γ z) :
    LipschitzSpanningDisk g γ := by
  let K := (exists_disk_lipschitz_constant g hF).choose
  have hK := (exists_disk_lipschitz_constant g hF).choose_spec
  exact {
    map := F
    continuous_on_disk := hF.continuous.continuousOn
    ae_manifold_differentiable := Filter.Eventually.of_forall
      (fun z _ => hF.mdifferentiableAt one_ne_zero)
    reparameterization := {
      map := id
      inverse := id
      left_inverse := fun _ => rfl
      right_inverse := fun _ => rfl
      continuous_map := continuous_id
      continuous_inverse := continuous_id }
    boundary_eq := hboundary
    lipschitz_constant := K
    lipschitz_nonnegative := hK.1
    lipschitz_on_disk := hK.2
    area_integrable := integrableOn_parametrizedAreaDensity g hF
    area_nonnegative := parametrizedRiemannianArea_nonneg g F }

/-- The assembled disk uses the exact metric area of the supplied map.
Source: MT Definition 18.17, printed p. 430. -/
theorem spanningDiskOfC1_area (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) (F : LoopPlane → M)
    (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) (hboundary : ∀ z : LoopCircle, F z.val = γ z) :
    (spanningDiskOfC1 g γ F hF hboundary).area = parametrizedRiemannianArea g F := rfl

/-- Every sufficiently short loop has an actual Lipschitz spanning disk.
This intermediate result includes finite area, but no uniform small-area
estimate. Source: MT Corollary 18.28, printed p. 434. -/
theorem exists_lipschitz_disk_of_short [T2Space M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M)) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ γ : C1FreeLoopSpace (M := M), freeLoopLength g γ < ζ →
      Nonempty (LipschitzSpanningDisk g γ) := by
  obtain ⟨ζ, hζ, hext⟩ := exists_c1_disk_extension_of_short g hcompact
  refine ⟨ζ, hζ, ?_⟩
  intro γ hγ
  obtain ⟨F, hF, hboundary⟩ := hext γ hγ
  exact ⟨spanningDiskOfC1 g γ F hF hboundary⟩

end PoincareMT.LoopSpace
