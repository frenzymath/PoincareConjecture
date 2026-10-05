import PoincareLib.Topology.Manifold.ConnectedSum.SphereReduction

/-!
# M74 connected-sum reduction statement

Natural-language theorem statement: for a finite family of genuine smooth
summand carriers, a genuine `SmoothFiniteConnectedSumAssembly` ending at a
nonempty connected carrier `C`, and a concrete diffeomorphism from every summand to
`ThreeSphere`, perform the finite relation induction and return a concrete
diffeomorphism from `C` to `ThreeSphere`.

This is Morgan--Tian Corollary 15.4(2), printed pp. 358--359, applied after
Proposition 15.3; source text is `references/derived/MT2007.txt:17861-17902`.
M72 must construct the assembly and M73 must supply the per-factor fields.
M74 itself accepts neither a sphere-sum diffeomorphism nor either Poincare
endpoint.  The nonempty and connected target fields prevent a zero-step
disjoint-union assembly from being silently treated as a sphere.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

def M74ConnectedSumReductionStatement : Prop :=
  ∀ {n : ℕ} (pieces : Fin n → GeneralizedSliceCarrier.{u})
    (C : GeneralizedSliceCarrier.{u})
    (_I : M74ReductionInput pieces C),
    Nonempty (M74ReductionConclusion C)

end PoincareMT
