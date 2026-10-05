import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessData

/-!
Adapted from Mapher `PoincareMT/Statements/M35StandardCapUniqueness.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M35 repaired standard-cap uniqueness and estimates statement

Every M34 standard-cap existence package satisfies the repaired uniqueness,
including common-domain equality with every compatible partial standard flow,
as well as the scalar lower rate and canonical-alternative package on its
selected flow.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedStandardCapUniquenessTheory : Prop where
  estimates : ∀ g₀ : StandardInitialMetric,
    ∀ E : RepairedStandardCapExistenceData g₀,
      Nonempty (RepairedStandardCapUniquenessData g₀ E)

end PoincareMT
