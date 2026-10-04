import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.UnboundedComplementComponent
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Ambient homeomorphisms preserve bounded complementary regions

Bounded components of a complement are defined without a
separation assumption. Proper metric spaces let an ambient
homeomorphism preserve their boundedness, closures and frontiers.
See Alexander 1924, pp. 7--8 and M76 derivation 247.
-/

set_option autoImplicit false

open Set Metric

namespace Set

/-- The union of bounded connected components of a complement.
No nonemptiness or connectedness is built into this definition.
See Alexander p. 7 and M76 derivation 247. -/
def boundedComplement {X : Type*} [MetricSpace X] (s : Set X) : Set X :=
  {x | x ∈ sᶜ ∧ Bornology.IsBounded (connectedComponentIn sᶜ x)}

/-- For a closed set in a locally connected metric space, the
union of its bounded complementary components is open.
See Alexander p. 7 and M76 derivation 247. -/
theorem isOpen_boundedComplement {X : Type*} [MetricSpace X]
    [LocallyConnectedSpace X] {s : Set X} (hs : IsClosed s) :
    IsOpen (boundedComplement s) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  refine ⟨connectedComponentIn sᶜ x, ?_, hs.isOpen_compl.connectedComponentIn,
    mem_connectedComponentIn hx.1⟩
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx.2

/-- The bounded components of the complement of a bounded set
are uniformly bounded in real dimension greater than one.
The connected exterior of one containing ball lies in the
unbounded component. See Alexander p. 7 and derivation 247. -/
theorem isBounded_boundedComplement {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : Bornology.IsBounded s)
    (hdim : 1 < Module.rank ℝ E) : Bornology.IsBounded (boundedComplement s) := by
  let : Nontrivial E := rank_pos_iff_nontrivial.mp (lt_trans zero_lt_one hdim)
  obtain ⟨r, hsr⟩ := hs.subset_closedBall (0 : E)
  have hext := isConnected_compl_closedBall_zero (E := E) hdim r
  have hextsub : (closedBall (0 : E) r)ᶜ ⊆ sᶜ := compl_subset_compl.mpr hsr
  have hextunb : ¬ Bornology.IsBounded (closedBall (0 : E) r)ᶜ := by
    intro h
    apply NormedSpace.unbounded_univ ℝ E
    simpa only [union_compl_self] using
      (isBounded_closedBall (x := (0 : E)) (r := r)).union h
  apply (isBounded_closedBall (x := (0 : E)) (r := r)).subset
  intro x hx
  by_contra hxr
  exact hextunb (hx.2.subset
    (hext.isPreconnected.subset_connectedComponentIn hxr hextsub))

end Set

namespace Homeomorph

variable {X Y : Type*} [MetricSpace X] [ProperSpace X]
  [MetricSpace Y] [ProperSpace Y]

/-- Homeomorphisms between proper metric spaces preserve and
reflect boundedness, using the compact closure of each bounded
set. No Lipschitz assumption is needed. See Alexander pp. 7--8
and M76 derivation 247. -/
theorem isBounded_image_iff_of_proper (e : X ≃ₜ Y) (s : Set X) :
    Bornology.IsBounded (e '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro h
    have hb : Bornology.IsBounded (e.symm '' (e '' s)) :=
      (h.isCompact_closure.image e.symm.continuous).isBounded.subset (image_mono subset_closure)
    simpa only [image_image, e.symm_apply_apply, image_id'] using hb
  · intro h
    exact (h.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)

/-- An ambient homeomorphism identifies the exact union of
bounded complementary components before and after deformation.
See Alexander pp. 7--8 and M76 derivation 247. -/
theorem image_boundedComplement (e : X ≃ₜ Y) (s : Set X) :
    e '' boundedComplement s = boundedComplement (e '' s) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image]
  change (x ∈ sᶜ ∧ Bornology.IsBounded (connectedComponentIn sᶜ x)) ↔
    (e x ∈ (e '' s)ᶜ ∧ Bornology.IsBounded (connectedComponentIn (e '' s)ᶜ (e x)))
  rw [← e.image_compl s, e.injective.mem_set_image]
  by_cases hx : x ∈ sᶜ
  · rw [← e.image_connectedComponentIn hx, e.isBounded_image_iff_of_proper]
  · simp only [hx, false_and]

/-- Closed bounded-region carriers commute with the ambient
deformation. The two separate cap deformations may be applied
to this statement separately. See Alexander pp. 7--8 and
M76 derivation 247. -/
theorem image_closure_boundedComplement (e : X ≃ₜ Y) (s : Set X) :
    e '' closure (boundedComplement s) = closure (boundedComplement (e '' s)) := by
  rw [e.image_closure, e.image_boundedComplement]

/-- The frontier of the bounded complementary carrier is
transported by an ambient homeomorphism. See Alexander
pp. 7--8 and M76 derivation 247. -/
theorem image_frontier_boundedComplement (e : X ≃ₜ Y) (s : Set X) :
    e '' frontier (boundedComplement s) = frontier (boundedComplement (e '' s)) := by
  rw [e.image_frontier, e.image_boundedComplement]

end Homeomorph
