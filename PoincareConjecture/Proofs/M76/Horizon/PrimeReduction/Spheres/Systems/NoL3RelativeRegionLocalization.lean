import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeCapAvoidance
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HasNoPuncturedSphereComponents.exists_relative_region_component_localization
    {X E ι κ : Type*} [MetricSpace X] [Finite κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R Q₀ : Set X} (O₀ S : κ → Set X)
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hR : IsCompact R) (he : PLDomain e R) (hSR : ∀ i, S i ⊆ interior R)
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x)
    (i : κ) {D : Set X} (hD : IsCompact D) (hDc : IsConnected D)
    (hDR : D ⊆ interior R) (hDother : ∀ k, k ≠ i → Disjoint D (S k))
    (hmeet : (S i ∩ D).Nonempty) :
    ∃ (Q : Set X) (B : κ × Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
      (O : κ → Set X) (W : ∀ k, (S k × unitInterval) ≃ₜ closure (O k)) (a : X),
      let A := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
      let C := connectedComponentIn A a
      Q = R \ ⋃ k, O k ∧ IsCompact Q ∧ PLDomain e Q ∧
      HasNoPuncturedSphereComponents e f Q ∧
      (∀ k, IsOpen (O k) ∧ IsCompact (closure (O k)) ∧
        IsConnected (closure (O k)) ∧ closure (O k) ⊆ interior R) ∧
      Pairwise (fun k l => Disjoint (closure (O k)) (closure (O l))) ∧
      (∀ k z, (W k z : X) ∈ O k ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ k z, (W k z : X) ∈ S k ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ k, S k ⊆ closure (O k)) ∧
      frontier Q = frontier R ∪ ⋃ b, B b ∧
      Pairwise (fun b c => Disjoint (B b) (B c)) ∧
      (∀ b, B b ⊆ closure (O b.1)) ∧
      a ∈ S i ∪ D ∧ IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧
      S i ∪ D ⊆ interior C ∧ closure (O i) ⊆ interior C ∧
      IsCompact (C \ O i) ∧ PLDomain e (C \ O i) ∧
      HasNoPuncturedSphereComponents e f (C \ O i) ∧
      frontier (C \ O i) = frontier C ∪ (B (i,false) ∪ B (i,true)) ∧
      frontier (O i) = B (i,false) ∪ B (i,true) ∧
      ∀ x ∈ C \ O i, connectedComponentIn (C \ O i) x = connectedComponentIn Q x := by
  classical
  obtain ⟨Q,B,H,sB,O,W,hQQ,hnoQ,hQeq,hQ,hQPL,hO,hOdis,hinc,hBdis,hBsub,hfront,
      hW,hcenter,hopen,hS,hSC,hnest,havoid⟩ :=
    hno.exists_relative_cut_avoiding_cap O₀ S W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀ hdis₀
      hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis hR he hSR
      L g hg hgi hreal i hD hDother
  have hsconn := (sS i).isConnected
  have hZconn : IsConnected (S i ∪ D) :=
    IsConnected.union hmeet hsconn hDc
  have hZother (k) (hki : k ≠ i) : Disjoint (S i ∪ D) (closure (O k)) := by
    apply disjoint_union_left.mpr
    exact ⟨(hOdis (Ne.symm hki)).mono_left (hSC i),havoid k hki⟩
  obtain ⟨a,ha,hCc,hCconn,hCPL,hZC,hDcompact,hDPL,hDfront,hDno,hDcomponents⟩ :=
    (hQeq ▸ hnoQ).exists_selected_cut_component_domain O hR (fun k => (hO k).1)
      (fun k => (hO k).2.2.2) hOdis (hQeq ▸ hQPL) i hZconn
      (union_subset (hSR i) hDR) hZother
  let A := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
  let C := connectedComponentIn A a
  have hAa : a ∈ A := connectedComponentIn_subset A a (interior_subset (hZC ha))
  have hclosureInt : closure (O i) ⊆ interior A := by
    rw [(finite_collar_cut_geometry hR (fun k : {k : κ // k ≠ i} => (hO k.val).1)
      (fun k : {k : κ // k ≠ i} => (hO k.val).2.2.2)
      (fun k l hkl => hOdis (Subtype.val_injective.ne hkl))).2.1]
    intro x hx
    refine ⟨(hO i).2.2.2 hx,?_⟩
    intro h
    obtain ⟨k,hk⟩ := mem_iUnion.mp h
    exact disjoint_left.mp (hOdis (Ne.symm k.property)) hx hk
  obtain ⟨x,hx⟩ := hsconn.nonempty
  have hxC : x ∈ C := interior_subset (hZC (Or.inl hx))
  have hclosureC : closure (O i) ⊆ C := by
    have hh := (hO i).2.2.1.isPreconnected.subset_connectedComponentIn (hSC i hx)
      (hclosureInt.trans interior_subset)
    rwa [←connectedComponentIn_eq hxC] at hh
  have hAPL := (hQeq ▸ hQPL).restore_one_disjoint_collar O hR
    (fun k => (hO k).1) (fun k => (hO k).2.2.2) hOdis i
  let : LocallyPathConnectedSpace A := hAPL.locallyPathConnectedSpace
  obtain ⟨U,hU,hCU⟩ := exists_open_inter_of_relative_open (connectedComponentIn_subset A a)
    (isOpen_preimage_connectedComponentIn hAa)
  have hclosureCi : closure (O i) ⊆ interior C := by
    rw [interior_eq_inter_of_eq_inter_open hU hCU]
    exact fun x hx => ⟨hclosureC hx,hclosureInt hx⟩
  have hOf : frontier (O i) = B (i,false) ∪ B (i,true) := by
    have hh := (finite_collar_cut_geometry hR (fun k => (hO k).1)
      (fun k => (hO k).2.2.2) hOdis).2.2.2.1 i
    rw [←hQeq] at hh
    exact hh.symm.trans (hinc i)
  have hDf : frontier (C \ O i) = frontier C ∪ (B (i,false) ∪ B (i,true)) := by
    rw [(compact_collar_cut_geometry hCc (hO i).1 hclosureCi).2.2.1,hOf]
  refine ⟨Q,B,sB,O,W,a,hQeq,hQ,hQPL,hnoQ,hO,hOdis,hopen,hS,hSC,hfront,hBdis,hBsub,
    ha,hCc,hCconn,hCPL,hZC,hclosureCi,hDcompact,hDPL,hDno,hDf,hOf,?_⟩
  intro x hx
  rw [hQeq]
  exact hDcomponents x hx

end PoincareConjecture.M76
