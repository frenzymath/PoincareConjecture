import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutGraphCollapse
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalSphereCutComponents

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_sphere_cut_graph_collapse
    {X ι κ : Type*} [MetricSpace X] [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hU : IsOpen U) (hSU : ∀ i, S i ⊆ U) :
    ∃ (Q : Set X) (hfinite : Finite (ConnectedComponents Q))
      (B : κ × Bool → Set X) (H : ∀ b, S b.1 ≃ₜ B b)
      (_sB : ∀ b, ChartwisePLSphere e (B b)) (O : κ → Set X)
      (D : ConnectedComponents Q → Set X) (ends : κ → Bool → ConnectedComponents Q)
      (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i)),
      letI := hfinite
      letI : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
      letI : DecidableEq (ConnectedComponents Q) := Classical.decEq _
      ∃ q : C(R, CutGraph.carrier ends),
        Q = R \ ⋃ i, O i ∧ IsCompact Q ∧ PLDomain e Q ∧
        (∀ i, IsOpen (O i) ∧ IsCompact (closure (O i)) ∧
          IsConnected (closure (O i)) ∧ closure (O i) ⊆ U ∩ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (O i)) (closure (O j))) ∧
        (⋃ i, closure (O i)) ∪ Q = R ∧ Q \ U = R \ U ∧
        (∀ c, IsCompact (D c) ∧ PLDomain e (D c) ∧ IsConnected (D c) ∧ D c ⊆ Q ∧
          frontier (D c) = (D c ∩ frontier R) ∪ ⋃ b ∈ {b | ends b.1 b.2 = c}, B b) ∧
        Pairwise (fun c d => Disjoint (D c) (D d)) ∧ (⋃ c, D c) = Q ∧
        (∀ x : Q, D (ConnectedComponents.mk x) = connectedComponentIn Q x) ∧
        (∀ i c, closure (O i) ∩ D c =
          ⋃ b ∈ {b : Bool | ends i b = c}, B (i, b)) ∧
        (∀ i x, (W i (x, 0) : X) = H (i, false) x ∧
          (W i (x, 1) : X) = H (i, true) x) ∧
        (∀ i x, (W i (x, ⟨(1 / 2 : ℝ), by norm_num⟩) : X) = x) ∧
        (∀ v (x : R), (x : X) ∈ D v →
          (q x : CutGraph.Ambient (ConnectedComponents Q) κ) = CutGraph.vertex v) ∧
        (∀ i (x : R) (hi : (x : X) ∈ closure (O i)),
          q x = CutGraph.edgePath ends i (((W i).symm ⟨x, hi⟩).2)) := by
  classical
  obtain ⟨Q, B, H, sB, O, D, owner, hfinite, hQeq, hQ, hQPL, hO, hCC,
    _, hcover, houtside, _, hD, hDD, hDcover, _, _, hactual, hinc, W, hW, hcenter⟩ :=
    exists_original_sphere_cut_components S sS hdis hR he hSR hU hSU
  let := hfinite
  let : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
  let ends : κ → Bool → ConnectedComponents Q := fun i b => owner (i, b)
  obtain ⟨q, hqD, hqC⟩ := CutGraph.exists_closed_cut_graph_collapse R D
    (fun i => closure (O i)) (fun i b => B (i, b)) ends (fun i => S i) W
    (fun v => (hD v).1.isClosed) (fun _ => isClosed_closure) hDD hCC
    (by rw [hDcover, union_comm]; exact hcover) hinc
    (fun i b x => CutGraph.collar_port_iff_height (fun b => B (i, b))
      (fun b => H (i, b)) (W i) (hW i) b x)
  exact ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC⟩

end PoincareConjecture.M76
