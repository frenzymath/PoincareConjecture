import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.Compression.SupportedSlabRemoval
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarEnlargement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < p) := ⟨by norm_num⟩

private theorem offset_phase_ne_endpoints {a b r t theta : ℝ}
    (hr : 0 < r) (hgap : r < b - a) (hcomp : r < p - (b - a))
    (ht : t = r ∨ t = -r) (htheta : theta = a ∨ theta = b) :
    (a : C0) ≠ ((theta + t : ℝ) : C0) ∧
      (b : C0) ≠ ((theta + t : ℝ) : C0) := by
  rcases htheta with htheta | htheta
  · subst theta
    have haI : a ∈ Ico (a - r) (a - r + p) := by constructor <;> linarith
    have hbI : b ∈ Ico (a - r) (a - r + p) := by constructor <;> linarith
    have htI : a + t ∈ Ico (a - r) (a - r + p) := by
      rcases ht with rfl | rfl <;> constructor <;> linarith
    constructor
    · intro h
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico haI htI).mp h
      rcases ht with rfl | rfl <;> linarith
    · intro h
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hbI htI).mp h
      rcases ht with rfl | rfl <;> linarith
  · subst theta
    have haI : a ∈ Ico a (a + p) := ⟨le_rfl, by norm_num⟩
    have hbI : b ∈ Ico a (a + p) := by constructor <;> linarith
    have htI : b + t ∈ Ico a (a + p) := by
      rcases ht with rfl | rfl <;> constructor <;> linarith
    constructor
    · intro h
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico haI htI).mp h
      rcases ht with rfl | rfl <;> linarith
    · intro h
      have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hbI htI).mp h
      rcases ht with rfl | rfl <;> linarith

theorem ChartwisePLMap.exists_hamiltonZero_spherical_slab_removal
    {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hI : IsPLIrreducible e (latticeHandleDomain (Fin 0) (Fin 3) L0))
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)})
    {Nlower Nupper : Set X0}
    (lower : FrontierResidualModel e Nlower (hamiltonZeroCircleMap phi ⁻¹' {(a : C0)}))
    (upper : FrontierResidualModel e Nupper (hamiltonZeroCircleMap phi ⁻¹' {(b : C0)}))
    (theta : ℝ) (htheta : theta = a ∨ theta = b)
    {S : Set X0} (sph : ChartwisePLSphere e S)
    (hSphase : S ⊆ hamiltonZeroCircleMap phi ⁻¹' {(theta : C0)})
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) (HB : L.space ≃ₜ S)
    (c : E × ℝ → X0) {r : ℝ} (hr : 0 < r)
    (hgap : r < b - a) (hcomp : r < p - (b - a))
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hbase : ∀ z : L.space, c ((z : E), 0) = HB z)
    (hopen : IsOpen (c '' (L.space ×ˢ Ioo (-r) r)))
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (hphase : ∀ z ∈ L.space ×ˢ Icc (-r) r,
      hamiltonZeroCircleMap phi (c z) = ((theta + sign * z.2 : ℝ) : C0)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      PLDomain e (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∧
      frontier (hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        hamiltonZeroCircleMap psi ⁻¹' {(a : C0), (b : C0)} ∧
      ∃ (lowerNew : FrontierResidualModel e Nlower (hamiltonZeroCircleMap psi ⁻¹' {(a : C0)}))
        (upperNew : FrontierResidualModel e Nupper (hamiltonZeroCircleMap psi ⁻¹' {(b : C0)})),
        lowerNew.complexity + upperNew.complexity ≤ lower.complexity + upper.complexity ∧
        lowerNew.count + upperNew.count < lower.count + upper.count := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨D, _, ⟨ball⟩⟩ := hI.2 S (by
    rw [hamiltonZeroDomain_eq_univ, interior_univ]
    exact subset_univ _) ⟨sph⟩
  obtain ⟨t, ht, _, Dnew, ⟨ballNew⟩, hDnew, _⟩ :=
    ball.exists_bicollar_enlargement sph hI.1.cover hI.1.compatible
      L hL HB c hr hc hi hbase hopen
  have htI : t ∈ Icc (-r) r := by rcases ht with rfl | rfl <;> constructor <;> linarith
  have hnewphase : ∀ x ∈ c '' (L.space ×ˢ {t}),
      (Q0 (hamiltonZeroAmbientMap phi x)).2 = ((theta + sign * t : ℝ) : C0) := by
    rintro x ⟨z, hz, rfl⟩
    have hzt : z.2 = t := hz.2
    change hamiltonZeroCircleMap phi (c z) = _
    rw [hphase z ⟨hz.1, hzt.symm ▸ htI⟩, hzt]
  have hshift : sign * t = r ∨ sign * t = -r := by
    rcases ht with rfl | rfl <;> rcases hsign with rfl | rfl <;> simp
  obtain ⟨haTheta, hbTheta⟩ := offset_phase_ne_endpoints hr hgap hcomp hshift htheta
  obtain ⟨psi, hpsi, hhom, hid, heNew, hfNew, lowerNew, upperNew,
    hlc, huc, hln, hun, hlstrict, hustrict⟩ :=
    hphi.exists_hamiltonZero_supported_slab_removal hd F ha hab hb he hfront lower upper
      ballNew (theta + sign * t) haTheta hbTheta hnewphase
  refine ⟨psi, hpsi, hhom, hid, heNew, hfNew, lowerNew, upperNew, add_le_add hlc huc, ?_⟩
  obtain ⟨x, hx⟩ := sph.isConnected.nonempty
  have hxD : x ∈ Dnew := interior_subset (hDnew (ball.boundary_subset hx))
  have hxphase := hSphase hx
  rcases htheta with rfl | rfl
  · exact Nat.add_lt_add_of_lt_of_le (hlstrict ⟨x, hxphase, hxD⟩) hun
  · exact Nat.add_lt_add_of_le_of_lt hln (hustrict ⟨x, hxphase, hxD⟩)

end PoincareConjecture.M76
