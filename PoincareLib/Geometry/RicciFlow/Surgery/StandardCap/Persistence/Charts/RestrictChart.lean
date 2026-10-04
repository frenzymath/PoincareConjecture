import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Charts.OpenChartDiffeomorph

/-!
# Restriction of a partial diffeomorphism to an open source

The map and inverse are unchanged, while the target is the exact
image of the smaller source. This supplies nested physical charts
in Morgan--Tian, Lemma 16.8, pp. 372-373; M44 derivation 65.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M44

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace G N]

/-- Restrict a smooth partial chart to an open subset of its
source, retaining its literal maps. Source: the fixed buffer in
Lemma 16.8, pp. 372-373; M44 derivation 65. -/
def restrictChart (e : PartialDiffeomorph I J M N ∞)
    {V : Set M} (hV : IsOpen V) (hsub : V ⊆ e.source) :
    PartialDiffeomorph I J M N ∞ where
  toFun := e
  invFun := e.invFun
  source := V
  target := e '' V
  map_source' _ hx := mem_image_of_mem e hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    exact Eq.mpr (congrArg (fun z : M => z ∈ V) (e.toPartialEquiv.left_inv (hsub hx))) hx
  left_inv' _ hx := e.left_inv (hsub hx)
  right_inv' _ hy := e.right_inv (by
    obtain ⟨x, hx, rfl⟩ := hy
    exact e.map_source (hsub hx))
  open_source := hV
  open_target := e.toOpenPartialHomeomorph.isOpen_image_of_subset_source hV hsub
  contMDiffOn_toFun := e.contMDiffOn.mono hsub
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hsub hx))

/-- The target-valued chart sends any subset of its source to
the exact preimage of its ambient image. Source: the nested
physical buffer in Lemma 16.8; M44 derivation 65. -/
theorem targetChart_image_eq_preimage (e : PartialDiffeomorph I J M N ∞)
    (p : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens N))
    {V : Set M} (hsub : V ⊆ e.source) :
    targetChart e p '' V = Subtype.val ⁻¹' (e '' V) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (targetChart_val e p (hsub hx)).symm⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, Subtype.ext ((targetChart_val e p (hsub hx)).trans hxy)⟩

end PoincareMT.M44
