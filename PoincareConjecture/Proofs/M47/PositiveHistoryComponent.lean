import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveLocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

theorem component_cylinder_positive_iff
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (U : TopologicalSpace.Opens C.carrier)
    (e : SurgeryFlowCylinder F C origin scale I U)
    (hcompact : IsCompact (U : Set C.carrier))
    (hconnected : IsConnected (U : Set C.carrier))
    (s : ℝ) (hs : s ∈ I) (g : RiemannianMetric 3 U) (D : LeviCivitaData g)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w))
    (x : U) :
    (∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair g y v w → 0 < D.sectionalCurvature y v w) ↔
    SurgeryPositiveComponentAt F (origin + s / scale) (e.forward s hs x.val) := by
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => e.forward s hs y.val) := by
    intro y
    exact ((e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val (n := ∞) y)
  have hpoint (y : U) := Proofs.M46.sectional_positive_iff_of_local_isometry D
    (F.connection (origin + s / scale)) isOpen_univ hf.contMDiffOn
    (fun z _hz => hmetric z) (mem_univ y)
  have himage := M47.component_cylinder_image_eq e U.isOpen hcompact hconnected
    s hs x.property
  constructor
  · intro hpos y hy
    obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hy
    exact (hpoint ⟨z, hz⟩).mp (hpos ⟨z, hz⟩)
  · intro hpos y
    apply (hpoint y).mpr
    apply hpos _
    rw [← himage]
    exact mem_image_of_mem _ y.property

end PoincareConjecture.M47Positive
