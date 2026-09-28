import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Endpoint
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Periodicity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.Complexity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.ComplementarySourceSlab









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

private structure ComplementaryFrontierStage {α β : Type*}
    (e : α → OpenPartialHomeomorph X V3) (d : β → OpenPartialHomeomorph X V3)
    (phi : C(H, H)) (a b : ℝ) where
  map : C(H, H)
  support : Set X
  compact_support : IsCompact support
  support_interior : support ⊆ interior R
  fixed : ∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ support →
    map x = phi x
  pl : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L map)
  fromOriginal : phi.HomotopyRel map B
  fromIdentity : (ContinuousMap.id H).HomotopyRel map B
  domain : PLDomain e (sourceSlab map a b)
  complement_domain : PLDomain e (sourceSlab map b (a + p))
  frontier_eq : frontier (sourceSlab map a b) = (sourceSlab map a b ∩ frontier R) ∪
    (sourceSurface map (a : C) ∪ sourceSurface map (b : C))
  complement_frontier_eq : frontier (sourceSlab map b (a + p)) =
    (sourceSlab map b (a + p) ∩ frontier R) ∪
      (sourceSurface map (a : C) ∪ sourceSurface map (b : C))
  boundary_eq : map ⁻¹' B = phi ⁻¹' B
  model : FrontierResidualModel e (sourceSlab map a b) (frontier (sourceSlab map a b))

private theorem sourceSlab_nonempty_frontier_model
    {α : Type*} {e : α → OpenPartialHomeomorph X V3}
    (phi : C(H, H)) (F : (ContinuousMap.id H).HomotopyRel phi B) {a b : ℝ}
    (he : PLDomain e (sourceSlab phi a b)) {theta theta' : C}
    (hfront : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta')) :
    Nonempty (FrontierResidualModel e (sourceSlab phi a b) (frontier (sourceSlab phi a b))) := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hne : (frontier (sourceSlab phi a b)).Nonempty :=
    (sourceSurface_nonempty phi theta F).mono (fun _ hx => hfront.symm.subset (Or.inr (Or.inl hx)))
  exact he.nonempty_frontier_residual_model (sourceSlab_isCompact phi a b)
    (hne.mono he.closed.frontier_subset) isClosed_empty isClosed_frontier (by simp)
    (empty_union _).symm hne

theorem exists_complementary_sourceSlabs_frontier_kernels_at
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (sourceSlab phi a b))
    (he' : PLDomain e (sourceSlab phi b (a + p)))
    (hf : frontier (sourceSlab phi a b) = (sourceSlab phi a b ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hf' : frontier (sourceSlab phi b (a + p)) = (sourceSlab phi b (a + p) ∩ frontier R) ∪
      (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C))) :
    ∃ (psi : C(H, H)) (K : Set X), IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ K →
          psi x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
        Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
        psi ⁻¹' B = phi ⁻¹' B ∧
        ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          let N := sourceSlab psi uv.1 uv.2
          IsCompact N ∧ ∃ he : PLDomain e N,
            frontier N = (N ∩ frontier R) ∪
              (sourceSurface psi (uv.1 : C) ∪ sourceSurface psi (uv.2 : C)) ∧
            ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
              let M := sourceSurface psi (theta : C) \ frontier R
              ∃ hMF : M ⊆ frontier N, ∀ x : M, ∀ c : FundamentalGroup M x,
                FundamentalGroup.map
                  (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) x c = 1 →
                FundamentalGroup.map (ContinuousMap.inclusion hMF) x c = 1 := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have habq : (a : C) ≠ (b : C) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  have hdis (psi : C(H, H)) :
      Disjoint (sourceSurface psi (a : C)) (sourceSurface psi (b : C)) := by
    rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    exact disjoint_left.mpr (fun _ hx hy => habq (hx.2.symm.trans hy.2))
  obtain ⟨model⟩ := sourceSlab_nonempty_frontier_model phi F0 he hf
  let initial : ComplementaryFrontierStage e d phi a b :=
    ⟨phi, ∅, isCompact_empty, empty_subset _, fun _ _ => rfl, hphi,
      ContinuousMap.HomotopyRel.refl phi B, F0, he, he', hf, hf', rfl, model⟩
  have hex : ∃ n : ℕ, ∃ s : ComplementaryFrontierStage e d phi a b, s.model.complexity = n :=
    ⟨initial.model.complexity, initial, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hminimal (t : ComplementaryFrontierStage e d phi a b) :
      s.model.complexity ≤ t.model.complexity := by
    rw [hs]
    exact Nat.find_min' hex ⟨t, rfl⟩
  have hsupport (psi : C(H, H)) (A : Set X)
      (hfix : ∀ x : H,
        ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A → psi x = s.map x) :
      ∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ s.support ∪ A →
        psi x = phi x := by
    intro x hx
    exact (hfix x (fun h => hx (Or.inr (interior_subset h)))).trans
      (s.fixed x (fun h => hx (Or.inl h)))
  refine ⟨s.map, s.support, s.compact_support, s.support_interior, s.fixed,
    s.pl, ⟨s.fromOriginal⟩, ⟨s.fromIdentity⟩, s.boundary_eq, ?_⟩
  intro uv huv
  rcases huv with huv | huv
  · change uv = (a, b) at huv
    subst uv
    refine ⟨sourceSlab_isCompact s.map a b, s.domain, s.frontier_eq, ?_⟩
    intro theta htheta
    obtain ⟨hMF, halt⟩ := sourceSlab_endpoint_frontier_disk_alternative e s.map htheta
      s.domain s.frontier_eq (hdis s.map)
    refine ⟨hMF, ?_⟩
    intro x
    obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, havoid, hessential⟩ := halt x
    · exact hker
    · let rimF := (ContinuousMap.inclusion hMF).comp rim
      have hrimF (z : Metric.sphere (0 : Fin 2 → ℝ) 1) : (rimF z : X) = j z := (hjrim z).symm
      have hrimS (z : Metric.sphere (0 : Fin 2 → ℝ) 1) :
          j z ∈ sourceSurface s.map (theta : C) := by
        rw [hjrim z]
        exact (rim z).property.1
      obtain ⟨psi, A, hA, hAR, hfix, hpsi, ⟨Hfrom⟩, ⟨Fpsi⟩, _, hepsi, hfpsi,
          hBpsi, _, hecomp, hfcomp, newModel, hdec⟩ :=
        exists_supported_complementary_endpoint_decrease hd s.pl s.fromIdentity ha hab
          (by simpa only [zero_add] using hb) htheta s.complement_domain
          (sourceSlab_isCompact s.map a b) s.domain s.frontier_eq (hdis s.map) s.model
          hj hi hjN hproper havoid rimF hrimF hrimS hessential
      let t : ComplementaryFrontierStage e d phi a b :=
        ⟨psi, s.support ∪ A, s.compact_support.union hA, union_subset s.support_interior hAR,
          hsupport psi A hfix, hpsi, s.fromOriginal.trans Hfrom, Fpsi,
          hepsi, hecomp, hfpsi, hfcomp, hBpsi.trans s.boundary_eq, newModel⟩
      exact (Nat.not_lt_of_ge (hminimal t) hdec).elim
  · change uv = (b, a + p) at huv
    subst uv
    have hfm : frontier (sourceSlab s.map b (a + p)) =
        (sourceSlab s.map b (a + p) ∩ frontier R) ∪
          (sourceSurface s.map (b : C) ∪ sourceSurface s.map ((a + p : ℝ) : C)) := by
      simpa only [AddCircle.coe_add_period, union_comm] using s.complement_frontier_eq
    have hdm : Disjoint (sourceSurface s.map (b : C))
        (sourceSurface s.map ((a + p : ℝ) : C)) := by
      simpa only [AddCircle.coe_add_period] using (hdis s.map).symm
    obtain ⟨oldModel⟩ := sourceSlab_nonempty_frontier_model s.map s.fromIdentity
      s.complement_domain s.complement_frontier_eq
    have hcost := complementary_frontier_complexity_eq hd s.map s.pl s.fromIdentity ha hab hb
      s.frontier_eq s.complement_frontier_eq s.model oldModel
    refine ⟨sourceSlab_isCompact s.map b (a + p), s.complement_domain, hfm, ?_⟩
    intro theta htheta
    obtain ⟨hMF, halt⟩ := sourceSlab_endpoint_frontier_disk_alternative e s.map htheta
      s.complement_domain hfm hdm
    refine ⟨hMF, ?_⟩
    intro x
    obtain hker | ⟨j, rim, hj, hi, hjN, hjrim, hproper, havoid, hessential⟩ := halt x
    · exact hker
    · let rimF := (ContinuousMap.inclusion hMF).comp rim
      have hrimF (z : Metric.sphere (0 : Fin 2 → ℝ) 1) : (rimF z : X) = j z := (hjrim z).symm
      have hrimS (z : Metric.sphere (0 : Fin 2 → ℝ) 1) :
          j z ∈ sourceSurface s.map (theta : C) := by
        rw [hjrim z]
        exact (rim z).property.1
      have heperiod : PLDomain e (sourceSlab s.map (a + p) (b + p)) := by
        simpa only [sourceSlab_add_period] using s.domain
      obtain ⟨psi, A, hA, hAR, hfix, hpsi, ⟨Hfrom⟩, ⟨Fpsi⟩, _, hecomp, hfcomp,
          hBpsi, _, heperiod', hfperiod, newModel, hdec⟩ :=
        exists_supported_complementary_endpoint_decrease hd s.pl s.fromIdentity
          (show (a + b) / 2 < b by linarith)
          (show b < a + p by linarith)
          (show a + p < (a + b) / 2 + p by linarith)
          htheta heperiod (sourceSlab_isCompact s.map b (a + p)) s.complement_domain
          hfm hdm oldModel hj hi hjN hproper havoid rimF hrimF hrimS hessential
      have hepsi : PLDomain e (sourceSlab psi a b) := by
        simpa only [sourceSlab_add_period] using heperiod'
      have hfpsi : frontier (sourceSlab psi a b) = (sourceSlab psi a b ∩ frontier R) ∪
          (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
        simpa only [sourceSlab_add_period, AddCircle.coe_add_period, union_comm] using hfperiod
      have hfcomp' : frontier (sourceSlab psi b (a + p)) =
          (sourceSlab psi b (a + p) ∩ frontier R) ∪
            (sourceSurface psi (a : C) ∪ sourceSurface psi (b : C)) := by
        simpa only [AddCircle.coe_add_period, union_comm] using hfcomp
      obtain ⟨primaryModel⟩ := sourceSlab_nonempty_frontier_model psi Fpsi hepsi hfpsi
      have hnewcost := complementary_frontier_complexity_eq hd psi hpsi Fpsi ha hab hb
        hfpsi hfcomp' primaryModel newModel
      let t : ComplementaryFrontierStage e d phi a b :=
        ⟨psi, s.support ∪ A, s.compact_support.union hA, union_subset s.support_interior hAR,
          hsupport psi A hfix, hpsi, s.fromOriginal.trans Hfrom, Fpsi,
          hepsi, hecomp, hfpsi, hfcomp', hBpsi.trans s.boundary_eq, primaryModel⟩
      have ht : t.model.complexity < s.model.complexity := by
        change primaryModel.complexity < s.model.complexity
        rw [hnewcost, hcost]
        exact hdec
      exact (Nat.not_lt_of_ge (hminimal t) ht).elim

theorem exists_complementary_sourceSlabs_frontier_kernels
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (psi : C(H, H)) (K : Set X), IsCompact K ∧ K ⊆ interior R ∧
        (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ K →
          psi x = phi x) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
        Nonempty (phi.HomotopyRel psi B) ∧ Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
        psi ⁻¹' B = phi ⁻¹' B ∧
        ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
          let N := sourceSlab psi uv.1 uv.2
          IsCompact N ∧ ∃ he : PLDomain e N,
            frontier N = (N ∩ frontier R) ∪
              (sourceSurface psi (uv.1 : C) ∪ sourceSurface psi (uv.2 : C)) ∧
            ∀ theta ∈ ({uv.1, uv.2} : Set ℝ),
              let M := sourceSurface psi (theta : C) \ frontier R
              ∃ hMF : M ⊆ frontier N, ∀ x : M, ∀ c : FundamentalGroup M x,
                FundamentalGroup.map
                  (ContinuousMap.inclusion (hMF.trans he.closed.frontier_subset)) x c = 1 →
                FundamentalGroup.map (ContinuousMap.inclusion hMF) x c = 1 := by
  obtain ⟨a, haI, b, hbI, _, he, hf, _, he', hf', _⟩ :=
    exists_complementary_sourceSlabs_with_marked_corners e d hd phi hphi F0
  refine ⟨a, haI, b, hbI, ?_⟩
  exact exists_complementary_sourceSlabs_frontier_kernels_at e d hd phi hphi F0
    (by linarith [haI.1]) (by linarith [haI.2, hbI.1]) (by linarith [hbI.2]) he he' hf hf'

end PoincareConjecture.M76.HamiltonIntervalTorus
