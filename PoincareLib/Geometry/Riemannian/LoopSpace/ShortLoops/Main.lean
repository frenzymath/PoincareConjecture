import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Theory
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Triviality
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.SmallDisks

/-!
# Short-loop triviality and small-area disks

Morgan--Tian Lemma 18.27 and Corollary 18.28, printed pp. 434-435,
with Definition 18.17, p. 430, for admissible disks. Both decorated and raw
sphere-family conclusions are retained, along with the actual disk area.
Source revision and loop-model qualifications are recorded in
`references/ricci-flow/mapher/m58-short-loops.md`.

The proof uses a finite composition of local chart contractions and a
radial cutoff disk. Uniform metric derivative bounds and polar integration
give the small-area estimate for the contract's actual Lipschitz fillings.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Short-loop triviality and the corrected small-area disk threshold of
MT Lemma 18.27 and Corollary 18.28, printed pp. 434-435. -/
theorem repairedShortLoopTriviality : RepairedShortLoopTrivialityTheory.{u} := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro M _ _ _ _ _ g hcompact basepoint hpi
    exact LoopSpace.short_loop_family_trivial g hcompact basepoint hpi
  · intro M _ _ _ _ _ g hcompact hconnected basepoint hpi
    obtain ⟨ζ, hζ, hfamily⟩ :=
      LoopSpace.raw_short_loop_family_trivial g hcompact hconnected basepoint hpi
    exact ⟨ζ, hζ, fun source _ hlength => hfamily source hlength⟩
  · intro M _ _ _ _ _ g hcompact η hη
    exact LoopSpace.small_loop_filling g hcompact η hη

end PoincareMT
