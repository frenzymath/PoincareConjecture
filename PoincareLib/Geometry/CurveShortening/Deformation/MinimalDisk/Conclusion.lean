import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.AttainmentConclusion
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.GaussBonnet.Basic
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.FillingArea.Inequality

/-!
# The actual embedded filling-area inequality

Actual Plateau attainment and the proved supplied-disk Gauss--Bonnet
theorem discharge both geometric inputs of the first-variation proof.
MT Claim 19.5 and Lemma 19.4, pp. 439-441; derivations 41 and 45.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT

/-- The embedded filling-area inequality holds for the actual Ricci
flow, with the literal velocity residual and no analytic supplier
hypothesis. MT Claim 19.5 and Lemma 19.4, pp. 439-441; derivation 45. -/
theorem m65EmbeddedFillingAreaInequality_proved
    {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) :
    M65EmbeddedFillingAreaInequality F :=
  M65Filling.embedded_filling_area_inequality_of_attainment_gaussBonnet F
    (fun q _ => m65Plateau_attainment (F.metric q) (F.connection q))
    (fun q _ => m65SuppliedDiskGaussBonnet (F.metric q) (F.connection q))

end PoincareMT
