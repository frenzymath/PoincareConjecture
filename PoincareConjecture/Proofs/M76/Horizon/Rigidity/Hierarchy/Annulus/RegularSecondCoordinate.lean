import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateBoundaryLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.PhaseChart
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactCircleRegularLevel

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_second_coordinate_finite_regular_values {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    let q : C(R, C0) := (hamiltonZeroSecondCircleMap phi).comp
      ⟨Subtype.val, continuous_subtype_val⟩
    ∃ Z : Set C0, Z.Finite ∧ ∀ theta ∉ Z,
      (∀ x : R, q x = theta →
        ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
          (T : OpenPartialHomeomorph X0 V3),
          (a : C0) = theta ∧ ell.contLinear v = 1 ∧
          (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
          ∀ y : R, (y : X0) ∈ T.source → (q y = theta ↔ ell (T y) = 0)) ∧
      ∀ x : R, (x : X0) ∈ frontier R → q x = theta →
        ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3)
          (T : OpenPartialHomeomorph X0 V3),
          (a : C0) = theta ∧ psi.contLinear u = 1 ∧
          ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
          (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
          (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
          ∀ y : R, (y : X0) ∈ T.source → (q y = theta ↔ ell (T y) = 0) := by
  classical
  intro q
  choose i K w hK hxG hxK hKt hw hlift using
    exists_hamiltonZeroSecondCircleMap_lift e d hd phi hphi
  let U : X0 → Set X0 := fun x => (e (i x)).source ∩ e (i x) ⁻¹' interior (K x).space
  have hU (x : X0) : IsOpen (U x) :=
    (e (i x)).continuousOn.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  obtain ⟨s, hs⟩ := isCompact_hamiltonZeroAmbient.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxG x, hxK x⟩)
  choose G psi u KB wB hu hxGB hxzero hxKB hKB hKtB hwB halign hGB hGRB hliftB using
    fun x : frontier R => exists_hamiltonZero_second_coordinate_boundary_lift
      e d hd phi hphi he x x.property
  let UB : frontier R → Set X0 :=
    fun x => (G x).source ∩ G x ⁻¹' interior (KB x).space
  have hUB (x : frontier R) : IsOpen (UB x) :=
    (G x).continuousOn.isOpen_inter_preimage (G x).open_source isOpen_interior
  have hfront : IsCompact (frontier R) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset isClosed_frontier (subset_univ _)
  obtain ⟨sB, hsB⟩ := hfront.elim_finite_subcover UB hUB
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxGB ⟨x, hx⟩, hxKB ⟨x, hx⟩⟩)
  let Z : Set C0 :=
    (⋃ j : s, (fun z => (w j z : C0)) '' (K j).vertices) ∪
    (⋃ j : sB, (fun z => (wB j z : C0)) '' (KB j).vertices)
  have hZ : Z.Finite :=
    (finite_iUnion fun j : s => ((K j).finite_vertices_of_finite_faces (hK j)).image _).union
      (finite_iUnion fun j : sB => ((KB j).finite_vertices_of_finite_faces (hKB j)).image _)
  refine ⟨Z, hZ, ?_⟩
  intro theta htheta
  constructor
  · intro x hxt
    obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp (hs (mem_univ (x : X0)))
    have hvalue : (w j (e (i j) x) : C0) = theta := by
      have h := hlift j (e (i j) x) (interior_subset hxj.2)
      rw [(e (i j)).left_inv hxj.1] at h
      exact h.symm.trans hxt
    have hreg : ∀ z ∈ (K j).vertices, w j z ≠ w j (e (i j) x) := by
      intro z hz heq
      apply htheta
      exact Or.inl (mem_iUnion.mpr
        ⟨⟨j, hjs⟩, z, hz, (congrArg (fun r : ℝ => (r : C0)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hxT, hzero, hT, hformula, hlevel⟩ :=
      HamiltonIntervalTorus.exists_source_circle_height_chart e p q (e (i j))
        (fun k => he.compatible k (i j)) (K j) (hK j) (w j) (hw j)
        (fun y hy hyK => by
          have h := hlift j (e (i j) y) hyK
          rwa [(e (i j)).left_inv hy] at h)
        x hxj.1 hxj.2 hreg
    refine ⟨a, ell, v, T, ha.trans hxt, hv, hxT, hzero, hT, hformula, ?_⟩
    intro y hy
    simpa only [hxt] using hlevel y hy
  · intro x hx hxt
    obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp (hsB hx)
    have hvalue : (wB j (G j x) : C0) = theta :=
      (hliftB j x hxj.1 (interior_subset hxj.2)).symm.trans hxt
    have hreg : ∀ z ∈ (KB j).vertices, wB j z ≠ wB j (G j x) := by
      intro z hz heq
      apply htheta
      exact Or.inr (mem_iUnion.mpr
        ⟨⟨j, hjs⟩, z, hz, (congrArg (fun r : ℝ => (r : C0)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hpv, hxT, hzero, hpsi, hT, hTR, hTB, hformula, hlevel⟩ :=
      HamiltonIntervalTorus.exists_relative_circle_height_chart e p q (G j) (hGB j)
        (psi j) (u j) (hu j) (hGRB j) (KB j) (hKB j) (halign j) (wB j) (hwB j)
        (fun y hy hyK => hliftB j y hy hyK) x hx hxj.1 hxj.2 hreg
    refine ⟨a, psi j, ell, u j, v, T, ha.trans hxt, hu j, hv, hpv,
      hxT, hzero, hpsi, hT, hTR, hTB, hformula, ?_⟩
    intro y hy
    simpa only [hxt] using hlevel y hy

theorem exists_hamiltonZero_regular_second_coordinate {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    let q : C(R, C0) := (hamiltonZeroSecondCircleMap phi).comp
      ⟨Subtype.val, continuous_subtype_val⟩
    ∃ t ∈ Ioo (0 : ℝ) p,
      IsCompact (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(t : C0)}) ∧
      (∀ x : R, q x = (t : C0) →
        ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
          (T : OpenPartialHomeomorph X0 V3),
          (a : C0) = (t : C0) ∧ ell.contLinear v = 1 ∧
          (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
          ∀ y : R, (y : X0) ∈ T.source → (q y = (t : C0) ↔ ell (T y) = 0)) ∧
      ∀ x : R, (x : X0) ∈ frontier R → q x = (t : C0) →
        ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3)
          (T : OpenPartialHomeomorph X0 V3),
          (a : C0) = (t : C0) ∧ psi.contLinear u = 1 ∧
          ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (x : X0) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
          (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
          (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
          (∀ y : R, (y : X0) ∈ T.source → q y = ((ell (T y) + a : ℝ) : C0)) ∧
          ∀ y : R, (y : X0) ∈ T.source → (q y = (t : C0) ↔ ell (T y) = 0) := by
  intro q
  obtain ⟨Z, hZ, hregular⟩ :=
    exists_hamiltonZero_second_coordinate_finite_regular_values e d hd phi hphi he
  obtain ⟨t, ht, htZ⟩ := AddCircle.exists_representative_avoiding_finite p hZ
  refine ⟨t, ht, ?_, hregular (t : C0) htZ⟩
  exact isCompact_hamiltonZeroAmbient.of_isClosed_subset
    (he.closed.inter (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap phi).continuous))
    (subset_univ _)

end PoincareConjecture.M76
