import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Elimination
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Cap

/-!
# Whole strong tubes from neck centers

Use the terminal slices of the strong necks as the whole cover in the supplied
global theorem. Since there are no input caps, choose cap constant one.
The strict scalar-ratio bound rules out an output cap with this constant.
Completeness and noncompactness exclude the other global alternatives.

Reference: Morgan--Tian, Definition 9.82, p. 236; Corollary 9.88,
pp. 239--240; Proposition A.25, p. 514.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.NoncompactKappa

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The terminal necks form a cover with no caps and cap constant one. -/
def wholeNeckCover (K : AncientKappaSolution 3 M) {t epsilon epsilon₀ : ℝ}
    (hepsilon : 0 < epsilon) (hthreshold : 0 < epsilon₀)
    (hsmall : epsilon₀ ≤ 1 / 200) (hle : epsilon ≤ epsilon₀)
    (hstrong : ∀ x : M, ∃ N : StrongEvolvingNeck K t epsilon, N.center = x) :
    ConnectedNeckCapCover (K.flow.metric t) := {
  epsilon := epsilon
  epsilon_pos := hepsilon
  epsilon_threshold := epsilon₀
  epsilon_threshold_pos := hthreshold
  epsilon_threshold_le_one_two_hundred := hsmall
  epsilon_le_threshold := hle
  cap_constant := 1
  cap_constant_pos := by norm_num
  X := Set.univ
  connected_X := isConnected_univ
  necks := Set.range (fun N : StrongEvolvingNeck K t epsilon => N.terminal_neck)
  caps := ∅
  pointwise_cover := by
    intro x _
    obtain ⟨N, hN⟩ := hstrong x
    exact Or.inl ⟨N.terminal_neck, ⟨N, rfl⟩, N.terminal_center.trans hN⟩
  neck_epsilon := by
    rintro _ ⟨N, rfl⟩
    exact N.terminal_epsilon
  cap_epsilon := by simp
  cap_constant_bound := by simp }

/-- A single threshold works for every noncompact solution whose points are
strong neck centers. The balanced chain is supplied by the global theorem. -/
theorem exists_wholeStrongTube_threshold (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M) {t epsilon : ℝ},
        t ≤ 0 → 0 < epsilon → epsilon ≤ epsilon₀ →
        ¬ IsCompact (Set.univ : Set M) →
        (∀ x : M, ∃ N : StrongEvolvingNeck K t epsilon, N.center = x) →
        Nonempty (M26StrongTube K t epsilon) := by
  obtain ⟨epsilon₀, hpos, hsmall, hglobal⟩ := P.global_neck_cap
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ K t epsilon ht hepsilon hle hnoncompact hstrong
  let H := wholeNeckCover K hepsilon hpos hsmall hle hstrong
  obtain ⟨conclusion⟩ := hglobal (K.flow.metric t) H hle rfl
  rcases conclusion.tube_or_capped_of_noncompact (K.complete t ht) hnoncompact with
    ⟨tube, he, hwhole⟩ | ⟨tube, hwhole, hcap, he, hconstant⟩
  · exact ⟨{
      time_mem := ht
      epsilon_pos := hepsilon
      tube := tube
      strong_at := fun x => by
        obtain ⟨N, hN⟩ := hstrong x
        exact ⟨N, hN, by simp only [hwhole, Set.mem_univ]⟩
      tube_epsilon := he
      carrier_eq_univ := hwhole }⟩
  · exact (not_le_of_gt tube.cap.one_lt_cap_constant hconstant).elim

end PoincareMT.NoncompactKappa
