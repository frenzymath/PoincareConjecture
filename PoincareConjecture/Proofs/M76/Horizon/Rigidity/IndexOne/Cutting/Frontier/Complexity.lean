import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.PLPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Frontier.Components
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PLSurfaceCount










set_option autoImplicit false
open Set Metric Geometry
open scoped BigOperators

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

theorem complementary_frontier_complexity_eq
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hfront : frontier (sourceSlab phi a b) =
      (sourceSlab phi a b ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (hfront' : frontier (sourceSlab phi b (a + p)) =
      (sourceSlab phi b (a + p) ∩ frontier R) ∪
        (sourceSurface phi (a : C) ∪ sourceSurface phi (b : C)))
    (M : FrontierResidualModel e (sourceSlab phi a b) (frontier (sourceSlab phi a b)))
    (M' : FrontierResidualModel e (sourceSlab phi b (a + p))
      (frontier (sourceSlab phi b (a + p)))) : M.complexity = M'.complexity := by
  classical
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  have hR := isCompact_latticeHandleDomain (Fin 1) (Fin 2) L
  let : CompactSpace R := isCompact_iff_compactSpace.mp hR
  let phase : C(R, C) := (sourcePhase phi).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have hNc : IsCompact (sourceSlab phi b (a + p)) :=
    (((AddCircle.isCompact_closedIntervalArc p b (a + p)).isClosed.preimage phase.continuous).isCompact).image
      continuous_subtype_val
  obtain ⟨G, hfix, hstrip⟩ := exists_complementary_frontier_homeomorph phi F ha hab hb hfront hfront'
  obtain ⟨r, hr⟩ := exists_residualModel_component_equiv M M' G
  have hres (i : Fin M.count) : M.residual i = M'.residual (r i) := by
    let A := M.complex.edgeComponentComplex (M.pick i)
    let A' := M'.complex.edgeComponentComplex (M'.pick (r i))
    have hA : A.faces.Finite := M.finite.subset (M.complex.edgeComponentComplex_le _)
    have hA' : A'.faces.Finite := M'.finite.subset (M'.complex.edgeComponentComplex_le _)
    have hAsub : A.space ⊆ M.complex.space :=
      SimplicialComplex.space_subset_of_le (M.complex.edgeComponentComplex_le _)
    have hA'sub : A'.space ⊆ M'.complex.space :=
      SimplicialComplex.space_subset_of_le (M'.complex.edgeComponentComplex_le _)
    have hmap (z) (hz : z ∈ A.space) : M.map z ∈ M.components i :=
      (M.images i).symm.subset ⟨z, hz, rfl⟩
    have hmap' (z) (hz : z ∈ A'.space) : M'.map z ∈ M'.components (r i) :=
      (M'.images (r i)).symm.subset ⟨z, hz, rfl⟩
    obtain ⟨x0, hx0⟩ := (M.component i).2.1.nonempty
    let q : (M.vertices → ℝ × V3) → frontier (sourceSlab phi a b) := fun z =>
      if hz : z ∈ A.space then ⟨M.map z, (M.component i).2.2.1 (hmap z hz)⟩
      else ⟨x0, (M.component i).2.2.1 hx0⟩
    have hqval (z) (hz : z ∈ A.space) : (q z : X) = M.map z := by simp only [q, dif_pos hz]
    have hqPL : PolyhedralPLInCharts e (fun z => (q z : X)) A.space :=
      (M.pl.restrict_finite A hA hAsub).congr (fun z hz => (hqval z hz).symm)
    have hqc : ContinuousOn q A.space :=
      Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hqPL.continuousOn
    let f := fun z => M'.coordinates (G (q z))
    have hf : FinitePiecewiseAffineOn f A.space :=
      finitePiecewiseAffineOn_complementary_frontier_coordinate hd phi hphi F ha hab hb hfront
        (fun x => (G x : X)) hfix hstrip A hA q hqc hqPL M'.coordinates M'.coordinates_pl
    have hfi : InjOn f A.space := by
      intro z hz w hw hzw
      have hG : G (q z) = G (q w) := Subtype.ext
        (M'.coordinates_injective (hNc.isClosed.frontier_subset (G (q z)).property)
          (hNc.isClosed.frontier_subset (G (q w)).property) hzw)
      have hqeq := congrArg Subtype.val (G.injective hG)
      rw [hqval z hz, hqval w hw] at hqeq
      exact M.injective (hAsub hz) (hAsub hw) hqeq
    have hfs : f '' A.space = A'.space := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        have hqS : (q z : X) ∈ M.components i := (hqval z hz).symm ▸ hmap z hz
        have hGS := (hr i (q z)).mp hqS
        obtain ⟨w, hw, hwG⟩ := (M'.images (r i)).subset hGS
        change M'.coordinates (G (q z)) ∈ A'.space
        rw [← hwG, M'.inverse w (hA'sub hw)]
        exact hw
      · intro w hw
        let y : frontier (sourceSlab phi b (a + p)) :=
          ⟨M'.map w, (M'.component (r i)).2.2.1 (hmap' w hw)⟩
        have hxS : (G.symm y : X) ∈ M.components i :=
          (hr i (G.symm y)).mpr (by simpa only [G.apply_symm_apply] using hmap' w hw)
        obtain ⟨z, hz, hzx⟩ := (M.images i).subset hxS
        have hqeq : q z = G.symm y := Subtype.ext ((hqval z hz).trans hzx)
        refine ⟨z, hz, ?_⟩
        change M'.coordinates (G (q z)) = w
        rw [hqeq, G.apply_symm_apply]
        exact M'.inverse w (hA'sub hw)
    have hEuler := hf.surfaceEulerCount_eq_of_injOn hA hA'
      (fun s hs => M.dimension s (M.complex.edgeComponentComplex_le _ hs))
      (fun s hs => M'.dimension s (M'.complex.edgeComponentComplex_le _ hs)) hfi hfs
    change (M.complex.edgeComponentComplex (M.pick i)).surfaceEulerCount =
      (M'.complex.edgeComponentComplex (M'.pick (r i))).surfaceEulerCount at hEuler
    rw [M.euler i, M'.euler (r i)] at hEuler
    omega
  unfold FrontierResidualModel.complexity
  calc
    (∑ i : Fin M.count, (M.residual i - 1)) =
        ∑ i : Fin M.count, (M'.residual (r i) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hres i]
    _ = ∑ j : Fin M'.count, (M'.residual j - 1) := r.sum_comp (fun j => M'.residual j - 1)

end PoincareConjecture.M76.HamiltonIntervalTorus
