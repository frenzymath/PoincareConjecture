import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Regions.OriginalFiniteFrontierFilling
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Fill the actual finite original spherical frontier

Compactness and connectedness come from the unchanged cube-sphere
parametrizations. The actual component construction retains a nonempty
subfamily and all original PL and protection data. It does not construct
the terminal spherical stage itself. See Wall008 and Hamilton Lemma2.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The original complete sphere parametrization supplies compactness
and connectedness, without another geometric assumption.
See Wall008, section4. -/
theorem ChartwisePLSphere.compact_connected
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) : IsCompact S ∧ IsConnected S := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let : ConnectedSpace (sphere (0 : V3) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) 0 zero_le_one)
  let : CompactSpace S := s.parametrization.compactSpace
  let : ConnectedSpace S := s.parametrization.connectedSpace_iff.mp inferInstance
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    isConnected_iff_connectedSpace.mpr inferInstance⟩

/-- Once the actual finite terminal sphere family has been constructed,
fill all other complementary components in the original domain.
The retained spheres are the same sets and the same original maps;
all protected relative neighborhoods and both frontiers are exact.
See Wall008, sections1--5. -/
theorem exists_spherical_frontier_filling
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R)
    (hend : HasOneSimplyConnectedEnd R)
    (hK : PLDomain e K) (hKc : IsCompact K) (hKconn : IsConnected K) (hKR : K ⊆ R)
    (S : κ → Set X) (hS : ∀ i, Nonempty (ChartwisePLSphere e (S i)))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hSint : ∀ i, S i ⊆ interior R)
    (hfront : frontier K = frontier R ∪ ⋃ i, S i)
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (⋃ i, S i))
    (hprotect : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' K)) :
    ∃ (L : Set X) (J : Finset κ), J.Nonempty ∧
      IsCompact L ∧ IsConnected L ∧ K ⊆ L ∧ L ⊆ R ∧ PLDomain e L ∧
      frontier L = frontier R ∪ (⋃ i ∈ J, S i) ∧
      frontier ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' (⋃ i ∈ J, S i) ∧
      IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ) ∧
      ∀ P : Set X, (Subtype.val : R → X) ⁻¹' P ⊆
          interior ((Subtype.val : R → X) ⁻¹' K) →
        (Subtype.val : R → X) ⁻¹' P ⊆
          interior ((Subtype.val : R → X) ⁻¹' L) := by
  have hSc (i : κ) : IsCompact (S i) := by
    obtain ⟨s⟩ := hS i
    exact s.compact_connected.1
  have hSconn (i : κ) : IsConnected (S i) := by
    obtain ⟨s⟩ := hS i
    exact s.compact_connected.2
  exact exists_original_finite_frontier_filling hR hRconn hend hK hKc hKconn hKR
    S hSc hSconn hdisjoint hSint hfront hrel hprotect

end PoincareMT.M76
