import PoincareConjecture.Proofs.M76.Rigidity.MeridianCut
import Mathlib.Topology.Separation.Hausdorff









set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))



abbrev HamiltonMeridianClosedCut := D × Icc (0 : ℝ) p



noncomputable def hamiltonMeridianQuotient : C(HamiltonMeridianClosedCut, H) :=
  hamiltonMeridianCutMap.comp
    ⟨fun z => (z.1, (z.2 : ℝ)),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩



theorem hamiltonMeridianQuotient_surjective :
    Function.Surjective hamiltonMeridianQuotient := by
  intro z
  have hz : z ∈ hamiltonMeridianCutMap '' (univ ×ˢ Icc (0 : ℝ) p) :=
    hamiltonMeridianCutMap_image.symm.subset (mem_univ z)
  obtain ⟨⟨x, t⟩, ht, he⟩ := hz
  exact ⟨(x, ⟨t, ht.2⟩), he⟩




theorem isQuotientMap_hamiltonMeridianQuotient :
    Topology.IsQuotientMap hamiltonMeridianQuotient := by
  let : T2Space H := ((Homeomorph.refl D).prodCongr
    hamiltonSolidTorusCircleEquiv).isEmbedding.t2Space
  exact hamiltonMeridianQuotient.continuous.isClosedMap.isQuotientMap
    hamiltonMeridianQuotient.continuous hamiltonMeridianQuotient_surjective



theorem hamiltonMeridianQuotient_eq_iff (a b : HamiltonMeridianClosedCut) :
    hamiltonMeridianQuotient a = hamiltonMeridianQuotient b ↔
      a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
        ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
        ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0)) :=
  hamiltonMeridianCutMap_eq_iff a.1 b.1 a.2.property b.2.property



theorem hamiltonMeridianQuotient_mem_boundary (a : HamiltonMeridianClosedCut) :
    hamiltonMeridianQuotient a ∈ B ↔ ‖(a.1 : V2)‖ = 1 := by
  change (‖(a.1 : V2)‖ = 1 ∧ True) ↔ ‖(a.1 : V2)‖ = 1
  exact ⟨And.left, fun h => ⟨h, trivial⟩⟩

end PoincareConjecture.M76
