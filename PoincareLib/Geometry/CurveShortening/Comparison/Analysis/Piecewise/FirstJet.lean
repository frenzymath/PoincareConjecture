import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differentiability of piecewise maps with matching first jets

Matching values and derivatives suffice at the join; no agreement of
higher derivatives is required. This is used for the straight boundary
contact in MT Claim 19.40; see the minimal-contact derivation, Section 9.
-/

set_option autoImplicit false

open Set

namespace PoincareMT

/-- Choosing between maps with the same value and derivative preserves that derivative,
independently of the geometry of the selection set. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Section 9. -/
theorem m64HasFDerivAt_piecewise_of_same_jet
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {D : E →L[𝕜] F} {x : E}
    (hf : HasFDerivAt f D x) (hg : HasFDerivAt g D x) (hval : f x = g x)
    (S : Set E) [DecidablePred (fun y => y ∈ S)] :
    HasFDerivAt (S.piecewise f g) D x := by
  have hleft : HasFDerivWithinAt (S.piecewise f g) D S x :=
    hf.hasFDerivWithinAt.congr (fun y hy => piecewise_eq_of_mem S f g hy)
      (by by_cases hx : x ∈ S <;> simp [hx, hval])
  have hright : HasFDerivWithinAt (S.piecewise f g) D Sᶜ x :=
    hg.hasFDerivWithinAt.congr (fun y hy => piecewise_eq_of_notMem S f g hy)
      (by by_cases hx : x ∈ S <;> simp [hx, hval])
  have h := hleft.union hright
  rwa [union_compl_self, hasFDerivWithinAt_univ] at h

/-- The one-variable version retains the literal derivative vector of either branch when
their values and first derivatives agree. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Section 9. -/
theorem m64HasDerivAt_piecewise_of_same_jet
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : 𝕜 → F} {v : F} {x : 𝕜}
    (hf : HasDerivAt f v x) (hg : HasDerivAt g v x) (hval : f x = g x)
    (S : Set 𝕜) [DecidablePred (fun y => y ∈ S)] :
    HasDerivAt (S.piecewise f g) v x :=
  m64HasFDerivAt_piecewise_of_same_jet hf.hasFDerivAt hg.hasFDerivAt hval S

end PoincareMT
