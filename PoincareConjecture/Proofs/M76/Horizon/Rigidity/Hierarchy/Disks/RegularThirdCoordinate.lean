import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateBoundaryLifts
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



def CircleCoordinateRegularity {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (R : Set X)
    {period : ℝ} (q : C(X, AddCircle period)) (theta : AddCircle period) : Prop :=
  (∀ x : R, q x = theta →
    ∃ (a : ℝ) (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (T : OpenPartialHomeomorph X V3),
      (a : AddCircle period) = theta ∧ ell.contLinear v = 1 ∧
      (x : X) ∈ T.source ∧ ell (T x) = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : AddCircle period)) ∧
      ∀ y : R, (y : X) ∈ T.source → (q y = theta ↔ ell (T y) = 0)) ∧
  ∀ x : R, (x : X) ∈ frontier R → q x = theta →
    ∃ (a : ℝ) (psi ell : V3 →ᴬ[ℝ] ℝ) (u v : V3) (T : OpenPartialHomeomorph X V3),
      (a : AddCircle period) = theta ∧ psi.contLinear u = 1 ∧
      ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
      (x : X) ∈ T.source ∧ ell (T x) = 0 ∧ psi (T x) = 0 ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ T.source, y ∈ R ↔ 0 ≤ psi (T y)) ∧
      (∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) ∧
      (∀ y : R, (y : X) ∈ T.source → q y = ((ell (T y) + a : ℝ) : AddCircle period)) ∧
      ∀ y : R, (y : X) ∈ T.source → (q y = theta ↔ ell (T y) = 0)

theorem exists_finite_regular_circle_values_of_original_lifts
    {X ι : Type*} [TopologicalSpace X] (e : ι → OpenPartialHomeomorph X V3)
    (period : ℝ) [Fact (0 < period)] (q : C(X, AddCircle period))
    (hX : IsCompact (univ : Set X)) {R : Set X} (he : PLDomain e R)
    (hloc : ∀ x : X, ∃ (i : ι) (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      K.faces.Finite ∧ x ∈ (e i).source ∧ e i x ∈ interior K.space ∧
      K.space ⊆ (e i).target ∧ K.AffineOnFaces w ∧
      ∀ z ∈ K.space, q ((e i).symm z) = (w z : AddCircle period)) :
    ∃ Z : Set (AddCircle period), Z.Finite ∧
      ∀ theta ∉ Z, CircleCoordinateRegularity e R q theta := by
  classical
  let qR : C(R, AddCircle period) := q.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hlocal := hloc
  choose i K w hK hxG hxK hKt hw hlift using hloc
  let U : X → Set X := fun x => (e (i x)).source ∩ e (i x) ⁻¹' interior (K x).space
  have hU (x : X) : IsOpen (U x) :=
    (e (i x)).continuousOn.isOpen_inter_preimage (e (i x)).open_source isOpen_interior
  obtain ⟨s, hs⟩ := hX.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxG x, hxK x⟩)
  choose G psi u KB wB hu hxGB hxzero hxKB hKB hKtB hwB halign hGB hGRB hliftB using
    fun x : frontier R => exists_circle_boundary_lift e period q he x x.property (hlocal x)
  let UB : frontier R → Set X :=
    fun x => (G x).source ∩ G x ⁻¹' interior (KB x).space
  have hUB (x : frontier R) : IsOpen (UB x) :=
    (G x).continuousOn.isOpen_inter_preimage (G x).open_source isOpen_interior
  have hfront : IsCompact (frontier R) :=
    hX.of_isClosed_subset isClosed_frontier (subset_univ _)
  obtain ⟨sB, hsB⟩ := hfront.elim_finite_subcover UB hUB
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxGB ⟨x, hx⟩, hxKB ⟨x, hx⟩⟩)
  let Z : Set (AddCircle period) :=
    (⋃ j : s, (fun z => (w j z : AddCircle period)) '' (K j).vertices) ∪
    (⋃ j : sB, (fun z => (wB j z : AddCircle period)) '' (KB j).vertices)
  have hZ : Z.Finite :=
    (finite_iUnion fun j : s => ((K j).finite_vertices_of_finite_faces (hK j)).image _).union
      (finite_iUnion fun j : sB => ((KB j).finite_vertices_of_finite_faces (hKB j)).image _)
  refine ⟨Z, hZ, ?_⟩
  intro theta htheta
  constructor
  · intro x hxt
    obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp (hs (mem_univ (x : X)))
    have hvalue : (w j (e (i j) x) : AddCircle period) = theta := by
      have h := hlift j (e (i j) x) (interior_subset hxj.2)
      rw [(e (i j)).left_inv hxj.1] at h
      exact h.symm.trans hxt
    have hreg : ∀ z ∈ (K j).vertices, w j z ≠ w j (e (i j) x) := by
      intro z hz heq
      apply htheta
      exact Or.inl (mem_iUnion.mpr
        ⟨⟨j, hjs⟩, z, hz, (congrArg (fun r : ℝ => (r : AddCircle period)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hxT, hzero, hT, hformula, hlevel⟩ :=
      HamiltonIntervalTorus.exists_source_circle_height_chart e period qR (e (i j))
        (fun k => he.compatible k (i j)) (K j) (hK j) (w j) (hw j)
        (fun y hy hyK => by
          have h := hlift j (e (i j) y) hyK
          rwa [(e (i j)).left_inv hy] at h)
        x hxj.1 hxj.2 hreg
    refine ⟨a, ell, v, T, ha.trans hxt, hv, hxT, hzero, hT, hformula, ?_⟩
    intro y hy
    change qR y = theta ↔ ell (T y) = 0
    simpa only [show qR x = theta from hxt] using hlevel y hy
  · intro x hx hxt
    obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp (hsB hx)
    have hvalue : (wB j (G j x) : AddCircle period) = theta :=
      (hliftB j x hxj.1 (interior_subset hxj.2)).symm.trans hxt
    have hreg : ∀ z ∈ (KB j).vertices, wB j z ≠ wB j (G j x) := by
      intro z hz heq
      apply htheta
      exact Or.inr (mem_iUnion.mpr
        ⟨⟨j, hjs⟩, z, hz, (congrArg (fun r : ℝ => (r : AddCircle period)) heq).trans hvalue⟩)
    obtain ⟨a, ell, v, T, ha, hv, hpv, hxT, hzero, hpsi, hT, hTR, hTB, hformula, hlevel⟩ :=
      HamiltonIntervalTorus.exists_relative_circle_height_chart e period qR (G j) (hGB j)
        (psi j) (u j) (hu j) (hGRB j) (KB j) (hKB j) (halign j) (wB j) (hwB j)
        (fun y hy hyK => hliftB j y hy hyK) x hx hxj.1 hxj.2 hreg
    refine ⟨a, psi j, ell, u j, v, T, ha.trans hxt, hu j, hv, hpv,
      hxT, hzero, hpsi, hT, hTR, hTB, hformula, ?_⟩
    intro y hy
    change qR y = theta ↔ ell (T y) = 0
    simpa only [show qR x = theta from hxt] using hlevel y hy

abbrev HamiltonZeroThirdCoordinateRegularity {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (phi : C(H0, H0)) (theta : C0) : Prop :=
  CircleCoordinateRegularity e R (hamiltonZeroThirdCircleMap phi) theta



theorem exists_hamiltonZero_third_coordinate_finite_regular_values {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ Z : Set C0, Z.Finite ∧
      ∀ theta ∉ Z, HamiltonZeroThirdCoordinateRegularity e R phi theta :=
  exists_finite_regular_circle_values_of_original_lifts e p (hamiltonZeroThirdCircleMap phi)
    isCompact_hamiltonZeroAmbient he (exists_hamiltonZeroThirdCircleMap_lift e d hd phi hphi)

theorem exists_hamiltonZero_regular_third_coordinate {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) :
    ∃ t ∈ Ioo (0 : ℝ) p,
      IsCompact (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(t : C0)}) ∧
      HamiltonZeroThirdCoordinateRegularity e R phi (t : C0) := by
  obtain ⟨Z, hZ, hregular⟩ :=
    exists_hamiltonZero_third_coordinate_finite_regular_values e d hd phi hphi he
  obtain ⟨t, ht, htZ⟩ := AddCircle.exists_representative_avoiding_finite p hZ
  refine ⟨t, ht, ?_, hregular (t : C0) htZ⟩
  exact isCompact_hamiltonZeroAmbient.of_isClosed_subset
    (he.closed.inter (isClosed_singleton.preimage (hamiltonZeroThirdCircleMap phi).continuous))
    (subset_univ _)

end PoincareConjecture.M76
