import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalSphereCutGraphCollapse
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutGraphHomotopyRetract









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem exists_original_sphere_cut_graph_homotopy_retract
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
      ∃ (q : C(R, CutGraph.carrier ends)) (s : C(CutGraph.carrier ends, R)),
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
          q x = CutGraph.edgePath ends i (((W i).symm ⟨x, hi⟩).2)) ∧
        (q.comp s).Homotopic (ContinuousMap.id (CutGraph.carrier ends)) := by
  classical
  obtain ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC⟩ :=
    exists_original_sphere_cut_graph_collapse S sS hdis hR he hSR hU hSU
  let := hfinite
  let : Fintype (ConnectedComponents Q) := Fintype.ofFinite _
  have hnonempty (i : κ) : Nonempty (S i) := by
    obtain ⟨x, hx⟩ := (show (sphere (0 : V3) 1).Nonempty from
      NormedSpace.sphere_nonempty.mpr zero_le_one)
    exact ⟨(sS i).parametrization ⟨x, hx⟩⟩
  let : ∀ i, Nonempty (S i) := hnonempty
  have hport (i : κ) (b : Bool) (x : S i) :
      (W i (x, if b then 1 else 0) : X) ∈ D (ends i b) := by
    have hb : (W i (x, if b then 1 else 0) : X) ∈ B (i, b) := by
      cases b
      · simpa only [Bool.false_eq_true, if_false, (hW i x).1]
          using (H (i, false) x).property
      · simpa only [if_true, (hW i x).2] using (H (i, true) x).property
    exact ((hinc i (ends i b)).symm.subset (mem_iUnion₂.mpr ⟨b, rfl, hb⟩)).2
  obtain ⟨s, hqs⟩ := CutGraph.exists_homotopy_section_of_closed_cut_collapse R D
    (fun i => closure (O i)) (fun v => (hD v).2.1) (fun v => (hD v).2.2.1)
    (fun v => (hD v).2.2.2.1.trans (hQeq ▸ sdiff_subset))
    (fun i => (hO i).2.2.2.trans (inter_subset_right.trans interior_subset))
    (fun i => S i) W ends hport q hqD hqC
  exact ⟨Q, hfinite, B, H, sB, O, D, ends, W, q, s, hQeq, hQ, hQPL, hO, hCC,
    hcover, houtside, hD, hDD, hDcover, hactual, hinc, hW, hcenter, hqD, hqC, hqs⟩

end PoincareConjecture.M76
