import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseLinkSection
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConnectedSection
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderBaseExtremeCap

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_extreme_vertex_cap_ball (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 3) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hqK : q ∈ K.vertices) (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v)
    (hlink : (K.link q).vertexAbstractComplex.edgeGraph.Connected) :
    ∃ d : Set E, IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = β}) ∧
      (∀ x ∈ d, A x = β) ∧ d ∩ K.space = K.space ∩ {x | A x = β} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {q} d)
        (d ∪ (K.space ∩ {x | A x ≤ β})) := by
  classical
  let B : E →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ E β
  have hB (x : E) : B x = A x - β := rfl
  have hzero : {x | B x = 0} = {x | A x = β} := by
    ext x
    simp only [mem_ofPred_eq, hB, sub_eq_zero]
  have hreg : ∀ v ∈ K.vertices, B v ≠ 0 := by
    intro v hv
    rw [hB, sub_ne_zero]
    by_cases hvq : v = q
    · rw [hvq, hAq]
      exact hβ.ne
    · exact (hgap v hv hvq).ne'
  have hconn : IsConnected (K.space ∩ {x | B x = 0}) := by
    rw [hzero]
    exact K.isConnected_extreme_vertex_section hpure A hAq hβ hgap hlink
  obtain ⟨d, hd, hplane, hinter⟩ := K.exists_finitePL_disk_of_connected_regularSlice
    hdim B hK hreg hpure hcofaces hconn
  rw [hzero] at hd hplane hinter
  exact ⟨d, hd, hplane, hinter, K.extreme_vertex_cap_ball hpure A hqK hAq hβ hgap hd hplane⟩

end Geometry.SimplicialComplex
