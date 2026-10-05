import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.ImmersedComparison
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Conclusion

/-!
# The actual immersed filling-area comparison

The proved embedded filling inequality supplies the literal input to
the reviewed immersed transfer. MT Lemma 19.4; derivations 49 and 51.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT

/-- The actual selected M64 flow conclusion yields the immersed
filling comparison, with its embedded input discharged by the attained
least-area disks and their proved Gauss-Bonnet identity.
MT Lemma 19.4; derivation 51. -/
theorem m65ImmersedFillingAreaComparison_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (V : M64ThreeDimensionalFlowConclusion F) :
    M65ImmersedFillingAreaComparison F :=
  m65ImmersedFillingAreaComparison_of_embedded F V
    (m65EmbeddedFillingAreaInequality_proved F)

end PoincareMT
