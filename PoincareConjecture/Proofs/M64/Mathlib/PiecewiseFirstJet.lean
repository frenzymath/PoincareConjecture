import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Basic









set_option autoImplicit false

open Set

namespace PoincareConjecture




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




theorem m64HasDerivAt_piecewise_of_same_jet
    {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : 𝕜 → F} {v : F} {x : 𝕜}
    (hf : HasDerivAt f v x) (hg : HasDerivAt g v x) (hval : f x = g x)
    (S : Set 𝕜) [DecidablePred (fun y => y ∈ S)] :
    HasDerivAt (S.piecewise f g) v x :=
  m64HasFDerivAt_piecewise_of_same_jet hf.hasFDerivAt hg.hasFDerivAt hval S

end PoincareConjecture
