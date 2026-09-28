import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.HornTransport


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

def strongEndRegionCover (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (hstrong : ∀ x ∈ X,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x) :
    NeckOnlyCover (Q.extension.extended.metric T) where
  epsilon := terminalAccuracyFactor * H.epsilon
  epsilon_pos := mul_pos terminalAccuracyFactor_pos H.epsilon_pos
  epsilon_threshold := A.epsilon₀
  epsilon_threshold_pos := A.epsilon₀_pos
  epsilon_threshold_le_one_two_hundred := A.epsilon₀_le_one_two_hundred
  epsilon_le_threshold := hA
  X := X
  connected_X := hX
  necks := {N | ∃ S : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon),
    N = S.spatialNeck ((hA.trans A.epsilon₀_le_one_two_hundred).trans_lt (by norm_num)) ∧
      S.center ∈ X}
  pointwise_center_cover := by
    intro x hx
    obtain ⟨N, hcenter⟩ := hstrong x hx
    exact ⟨N.spatialNeck ((hA.trans A.epsilon₀_le_one_two_hundred).trans_lt (by norm_num)),
      ⟨N, rfl, hcenter ▸ hx⟩, hcenter⟩
  neck_epsilon := by rintro N ⟨S, rfl, _⟩; rfl



theorem exists_source_tube_of_strong_centers (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier) (hX : IsConnected X)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (hstrong : ∀ x ∈ X,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x) :
    Nonempty (CorrectedA19Conclusion (Q.extension.extended.metric T)
      (Q.strongEndRegionCover A hA X hX hstrong)) := by
  have hε : terminalAccuracyFactor * H.epsilon ≤ 1 / 200 := hA.trans A.epsilon₀_le_one_two_hundred
  have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 := hε.trans_lt (by norm_num)
  obtain ⟨horn, _, m, hm⟩ := Q.end_tube K e
  obtain ⟨x, hx⟩ := (e.tail_connected (max n m)).nonempty
  have hxX : (x : (Q.extension.extended.slice T).carrier) ∈ X :=
    htail ⟨x, e.nested (le_max_left _ _) hx, rfl⟩
  have hxhorn : (x : (Q.extension.extended.slice T).carrier) ∈ horn.carrier :=
    hm ⟨x, e.nested (le_max_right _ _) hx, rfl⟩
  obtain ⟨N₀, hcenter₀⟩ := horn.every_point_neck x hxhorn
  let P := N₀.spatialNeck hhalf
  obtain ⟨_, _, _, _, _, hsep₀⟩ := horn.boundary_sphere_smooth_transport_of_epsilon_le
    hε P hε (show N₀.center ∈ horn.carrier from hcenter₀.symm ▸ hxhorn)
  have hcover : ∀ x ∈ X, ∃ N : EpsilonNeck (Q.extension.extended.metric T),
      N.epsilon ≤ 1 / 200 ∧ N.center = x := by
    intro x hx
    obtain ⟨N, hN⟩ := hstrong x hx
    exact ⟨N.spatialNeck hhalf, hε, hN⟩
  apply A.a19 (Q.extension.extended.metric T) (Q.strongEndRegionCover A hA X hX hstrong) hA
  rintro N ⟨S, rfl, hSX⟩
  let N := S.spatialNeck hhalf
  obtain ⟨D, L, _, _, hsphere⟩ :=
    EpsilonNeck.connected_center_smooth_transport_of_epsilon_le X hX.isPreconnected
      hcover P N hε hε (show N₀.center ∈ X from hcenter₀.symm ▸ hxX) hSX
  have hcomponent : D '' connectedComponent P.center = connectedComponent N.center := by
    have h := D.toHomeomorph.image_connectedComponentIn (s := univ) (x := P.center) (mem_univ _)
    simp only [connectedComponentIn_univ, image_univ, D.toHomeomorph.surjective.range_eq] at h
    apply h.trans
    symm
    apply connectedComponent_eq
    apply N.carrier_subset_connectedComponent
    apply N.central_sphere_subset
    rw [← hsphere]
    exact mem_image_of_mem D P.center_on_central_sphere
  exact (P.isSeparating_iff_of_homeomorph N D.toHomeomorph hcomponent hsphere).mp hsep₀

end PoincareConjecture.SingularLimitConclusion
