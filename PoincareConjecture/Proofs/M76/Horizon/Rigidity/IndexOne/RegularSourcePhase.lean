import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.SourcePhaseCover
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.PhaseChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCircleRegularLevel













set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem exists_phase_between_avoiding {Z : Set C} (hZ : Z.Finite)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ p) (hlt : lo < hi) :
    ∃ t ∈ Ioo lo hi, (t : C) ∉ Z := by
  have hinj : InjOn (fun t : ℝ => (t : C)) (Ioo lo hi) := by
    intro x hx y hy hxy
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
      (show x ∈ Ico 0 (0 + p) by constructor <;> linarith [hx.1, hx.2])
      (show y ∈ Ico 0 (0 + p) by constructor <;> linarith [hy.1, hy.2])).mp
    exact hxy
  obtain ⟨c, ⟨t, ht, rfl⟩, hc⟩ := ((Ioo_infinite hlt).image hinj).exists_notMem_finite hZ
  exact ⟨t, ht, hc⟩




theorem exists_sourcePhase_regular_level_between
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hhi : hi ≤ p) (hlt : lo < hi) :
    let q : C(R, C) := (sourcePhase phi).comp
      ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
        (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
    ∃ t ∈ Ioo lo hi,
      IsCompact (q ⁻¹' {(t : C)}) ∧ (q ⁻¹' {(t : C)}).Nonempty ∧
      (∀ x : R, q x = (t : C) →
        ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
          (T : OpenPartialHomeomorph X V3),
          (a : C) = (t : C) ∧ ell.contLinear v = 1 ∧
          (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ (y : R), (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C)) ∧
          ∀ (y : R), (y : X) ∈ T.source → (q y = (t : C) ↔ ell (T y) = 0)) ∧
      ∀ x : R, (x : X) ∈ frontier R → q x = (t : C) →
        ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3)
          (T : OpenPartialHomeomorph X V3),
          (a : C) = (t : C) ∧ psi.contLinear u = 1 ∧
          ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (x : X) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
          (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
          (∀ (y : R), (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C)) ∧
          ∀ (y : R), (y : X) ∈ T.source → (q y = (t : C) ↔ ell (T y) = 0) := by
  classical
  intro q
  obtain ⟨s, i, K, w, hK, _, hw, hlift, hcover⟩ :=
    exists_sourcePhase_finite_chart_cover e d hd phi hphi
  obtain ⟨sB, G, psi, u, KB, wB, hu, hKB, _, hwB, halign, hG, hGR, hliftB, hcoverB⟩ :=
    exists_sourcePhase_boundary_cover e d hd phi hphi
  let Z : Set C := (⋃ j : s, (fun z => (w j z : C)) '' (K j).vertices) ∪
    (⋃ j : sB, (fun z => (wB j z : C)) '' (KB j).vertices)
  have hZ : Z.Finite :=
    (finite_iUnion fun j => ((K j).finite_vertices_of_finite_faces (hK j)).image _).union
      (finite_iUnion fun j => ((KB j).finite_vertices_of_finite_faces (hKB j)).image _)
  obtain ⟨t, ht, htZ⟩ := exists_phase_between_avoiding hZ hlo hhi hlt
  let b : closedBall (0 : V1) 1 := ⟨fun _ => 1, by simp⟩
  have hb : ‖(b : V1)‖ = 1 := by simp [b]
  obtain ⟨x0, _, _, hx0⟩ := sourcePhase_boundary_surjective phi F b hb (t : C)
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  have hq0 : q (E.symm x0) = (t : C) := by
    change sourcePhase phi (E (E.symm x0)) = (t : C)
    rw [E.apply_symm_apply]; exact hx0
  let : CompactSpace R := isCompact_iff_compactSpace.mp
    (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L)
  refine ⟨t, ht, (isClosed_singleton.preimage q.continuous).isCompact,
    ⟨E.symm x0, hq0⟩, ?_, ?_⟩
  · intro x hxt
    obtain ⟨j, hxG, hxK⟩ := hcover x x.property
    have hvalue : (w j (e (i j) x) : C) = (t : C) :=
      (hlift j x hxG (interior_subset hxK)).symm.trans hxt
    have hreg : ∀ z ∈ (K j).vertices, w j z ≠ w j (e (i j) x) := by
      intro z hz heq
      apply htZ
      exact Or.inl (mem_iUnion.mpr ⟨j, z, hz, (congrArg (fun r : ℝ => (r : C)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hxT, hzero, hT, hformula, hlevel⟩ :=
      exists_source_circle_height_chart e p q (e (i j))
        (fun k => hphi.source_domain.compatible k (i j)) (K j) (hK j)
        (w j) (hw j) (hlift j) x hxG hxK hreg
    refine ⟨a, ell, v, T, ha.trans hxt, hv, hxT, hzero, hT, hformula, ?_⟩
    intro y hy
    simpa only [hxt] using hlevel y hy
  · intro x hx hxt
    obtain ⟨j, hxG, hxK⟩ := hcoverB x hx
    have hvalue : (wB j (G j x) : C) = (t : C) :=
      (hliftB j x hxG (interior_subset hxK)).symm.trans hxt
    have hreg : ∀ z ∈ (KB j).vertices, wB j z ≠ wB j (G j x) := by
      intro z hz heq
      apply htZ
      exact Or.inr (mem_iUnion.mpr ⟨j, z, hz, (congrArg (fun r : ℝ => (r : C)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hpv, hxT, hzero, hpsi, hT, hTR, hTB, hformula, hlevel⟩ :=
      exists_relative_circle_height_chart e p q (G j) (hG j) (psi j) (u j) (hu j)
        (hGR j) (KB j) (hKB j) (halign j) (wB j) (hwB j) (hliftB j) x hx hxG hxK hreg
    refine ⟨a, psi j, ell, u j, v, T, ha.trans hxt, hu j, hv, hpv, hxT,
      hzero, hpsi, hT, hTR, hTB, hformula, ?_⟩
    intro y hy
    simpa only [hxt] using hlevel y hy


theorem exists_sourcePhase_regular_level
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3)
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    let q : C(R, C) := (sourcePhase phi).comp
      ⟨latticeHandleDomainEquiv (Fin 1) (Fin 2) L,
        (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous⟩
    ∃ t ∈ Ioo (0 : ℝ) p,
      IsCompact (q ⁻¹' {(t : C)}) ∧ (q ⁻¹' {(t : C)}).Nonempty ∧
      (∀ x : R, q x = (t : C) →
        ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
          (T : OpenPartialHomeomorph X V3),
          (a : C) = (t : C) ∧ ell.contLinear v = 1 ∧
          (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ (y : R), (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C)) ∧
          ∀ (y : R), (y : X) ∈ T.source → (q y = (t : C) ↔ ell (T y) = 0)) ∧
      ∀ x : R, (x : X) ∈ frontier R → q x = (t : C) →
        ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3)
          (T : OpenPartialHomeomorph X V3),
          (a : C) = (t : C) ∧ psi.contLinear u = 1 ∧
          ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (x : X) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
          (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
          (∀ (y : R), (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C)) ∧
          ∀ (y : R), (y : X) ∈ T.source → (q y = (t : C) ↔ ell (T y) = 0) :=
  exists_sourcePhase_regular_level_between e d hd phi hphi F 0 p
    le_rfl le_rfl (by norm_num)

end PoincareConjecture.M76.HamiltonIntervalTorus
