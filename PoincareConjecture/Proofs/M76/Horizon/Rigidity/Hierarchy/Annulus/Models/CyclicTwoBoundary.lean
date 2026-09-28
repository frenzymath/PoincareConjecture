import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.CyclicSurfaceEulerCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryEulerBound
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CountZeroAnnulus









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

open Dehn.Annuli

open Classical in
theorem surfaceEulerCount_nonpos_of_two_boundaries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ side, L side ≤ K)
    (gamma : ∀ side, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L side).space)
    (hgamma : ∀ side, (gamma side).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ side, s ∈ (L side).faces then 1 else 2)
    : K.surfaceEulerCount ≤ 0 := by
  have hdis' : Pairwise (fun i j ↦ Disjoint (L i).space (L j).space) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  simpa using K.surfaceEulerCount_le_two_sub_boundary_circle_count
    hK hpure hconn hlinks L hLK hdis' gamma hgamma
    (by intro s hs hsc; simpa only [Bool.exists_bool] using hboundary s hs hsc)

open Classical in
theorem boundary_circle_count_le_two_of_isCyclic
    {E β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype β]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (L : β → SimplicialComplex ℝ E) (hLK : ∀ i, L i ≤ K)
    (hdis : Pairwise (fun i j ↦ Disjoint (L i).space (L j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (L i).faces then 1 else 2)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] : Nat.card β ≤ 2 := by
  have hlo := K.surfaceEulerCount_nonneg_of_isCyclic hK hconn x
  have hhi := K.surfaceEulerCount_le_two_sub_boundary_circle_count
    hK hpure hconn hlinks L hLK hdis gamma hgamma hcofaces
  omega

open Classical in
theorem exists_annulus_of_isCyclic_and_two_boundaries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsConnected K.space)
    (L : Bool → SimplicialComplex ℝ E) (hLK : ∀ side, L side ≤ K)
    (gamma : ∀ side, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (L side).space)
    (hgamma : ∀ side, (gamma side).IsFinitePL)
    (hdis : Disjoint (L false).space (L true).space)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ side, s ∈ (L side).faces then 1 else 2)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    ∃ A : squareAnnulus 8 1 ≃ₜ K.space, A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔ (A p : E) ∈ (L false).space) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔ (A p : E) ∈ (L true).space) := by
  have hzero : K.surfaceEulerCount = 0 := le_antisymm
    (surfaceEulerCount_nonpos_of_two_boundaries K hK hpure hlinks hconn L hLK
      gamma hgamma hdis hboundary)
    (K.surfaceEulerCount_nonneg_of_isCyclic hK hconn x)
  exact exists_annulus_of_count_zero K hK hpure hlinks hconn hzero L hLK
    gamma hgamma hdis hboundary

end PoincareConjecture.M76
