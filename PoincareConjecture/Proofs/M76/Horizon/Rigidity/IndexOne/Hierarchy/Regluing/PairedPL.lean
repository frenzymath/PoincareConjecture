import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PairedPLParameters

set_option autoImplicit false
open Set Metric Geometry
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem chartwisePLMap_of_standard_paired_slabs
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (he : PLDomain e R)
    (f : C(R, R)) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hslab : ∀ uv ∈ ({(a, b), (b, a + p)} : Set (ℝ × ℝ)),
      ∀ (K : SimplicialComplex ℝ V3), K.faces.Finite → ∀ q : V3 → R,
        PolyhedralPLInCharts d (fun z => (q z : X)) K.space →
        MapsTo (fun z => (q z : X)) K.space (sourceSlab (ContinuousMap.id H) uv.1 uv.2) →
        PolyhedralPLInCharts e (fun z => (f (q z) : X)) K.space) :
    ChartwisePLMap d e f := by
  classical
  have habC : (a : C) ≠ (b : C) := by
    intro h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico 0 (0 + p) from ⟨ha.le, by simpa using hab.trans hb⟩)
      (show b ∈ Ico 0 (0 + p) from ⟨(ha.trans hab).le, by simpa using hb⟩)).mp h
    exact hab.ne heq
  apply chartwisePLMap_of_embedded_polyhedral_parameters (E := V3) d e hd.domain he f
  intro x
  let phase : C(R, C) := (sourcePhase (ContinuousMap.id H)).comp
    ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
      (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
  have havailable : ∃ c v : ℝ, phase x ≠ (c : C) ∧
      ((c = a ∧ v = b) ∨ (c = b ∧ v = a + p)) := by
    by_cases hx : phase x = (a : C)
    · exact ⟨b, a + p, by rw [hx]; exact habC, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨a, b, hx, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨c, v, hxc, hcv⟩ := havailable
  obtain ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL, hseam⟩ :=
    exists_standard_parameter_avoiding_phase hd x c hxc
  obtain ⟨J, hJ, hpieces, hcover⟩ :=
    exists_finite_standard_slab_parameter_cover hd c v K hK q hqPL hseam
  let : Finite J := hJ.to_subtype
  have hpieces' (N : J) : N.val.faces.Finite ∧ N.val.space ⊆ K.space ∧
      (MapsTo (fun u => (q u : X)) N.val.space (sourceSlab (ContinuousMap.id H) a b) ∨
        MapsTo (fun u => (q u : X)) N.val.space (sourceSlab (ContinuousMap.id H) b (a + p))) := by
    obtain ⟨hN, hNK, hcase⟩ := hpieces N N.property
    refine ⟨hN, hNK, ?_⟩
    rcases hcv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcase
    · rcases hcase with h | h
      · exact Or.inr h
      · exact Or.inl (by simpa only [sourceSlab_add_period] using h)
  have hPL (N : J) : PolyhedralPLInCharts e (fun u => (f (q u) : X)) N.val.space := by
    obtain ⟨hN, hNK, hcase⟩ := hpieces' N
    have hqN := hqPL.restrict_finite N hN hNK
    rcases hcase with h | h
    · exact hslab (a, b) (Or.inl rfl) N hN q hqN h
    · exact hslab (b, a + p) (Or.inr rfl) N hN q hqN h
  have hcover' : K.space ⊆ ⋃ N : J, N.val.space := by
    intro u hu
    obtain ⟨N, hNJ, huN⟩ := mem_iUnion₂.mp (hcover hu)
    exact mem_iUnion.mpr ⟨⟨N, hNJ⟩, huN⟩
  have hfq : ContinuousOn (fun u => (f (q u) : X)) K.space :=
    continuous_subtype_val.comp_continuousOn (f.continuous.comp_continuousOn hq)
  exact ⟨K, q, z, hK, hq, hiq, hqz, hrange, hqPL,
    polyhedralPLInCharts_of_finite_cover he.cover he.compatible K hK
      (fun N : J => N.val) (fun N => (hpieces' N).1) hfq hPL hcover'⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
