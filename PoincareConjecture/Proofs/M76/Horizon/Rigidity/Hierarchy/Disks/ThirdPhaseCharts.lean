import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.RegularThirdCoordinate
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedCircleModel









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem CircleCoordinateRegularity.exists_marked_surface_chart
    {X ι : Type*} [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V3}
    {R : Set X} {period : ℝ} {q : C(X, AddCircle period)} {theta : AddCircle period}
    (hreg : CircleCoordinateRegularity e R q theta)
    (x : X) (hx : x ∈ R ∩ q ⁻¹' {theta}) :
    let S := R ∩ q ⁻¹' {theta}
    ∃ T : OpenPartialHomeomorph X V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source (frontier R)) ∨
        ∃ (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          psi.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∧
          ∀ y ∈ T.source, y ∈ frontier R ↔ psi (T y) = 0) := by
  classical
  let x' : R := ⟨x, hx.1⟩
  by_cases hxB : x ∈ frontier R
  · obtain ⟨a, psi, ell, u, v, T, _, hu, hv, huv, hxT, _, _, hcompat,
      hregion, hmark, _, hlevel⟩ := hreg.2 x' hxB hx.2
    refine ⟨T, hxT, hcompat, Or.inr ⟨ell, psi, u, v, hu, hv, huv, ?_, hmark⟩⟩
    intro y hy
    constructor
    · intro hyS
      exact ⟨(hlevel ⟨y, hyS.1⟩ hy).mp hyS.2, (hregion y hy).mp hyS.1⟩
    · rintro ⟨hz, hpos⟩
      have hyR := (hregion y hy).mpr hpos
      exact ⟨hyR, (hlevel ⟨y, hyR⟩ hy).mpr hz⟩
  · obtain ⟨a, ell, v, T, _, hv, hxT, _, hcompat, _, hlevel⟩ := hreg.1 x' hx.2
    let B := T.restrOpen (interior R) isOpen_interior
    have hxint : x ∈ interior R := (mem_interior_iff_notMem_frontier hx.1).mpr hxB
    refine ⟨B, ⟨hxT, hxint⟩, ?_, Or.inl ⟨ell, v, hv, ?_, ?_⟩⟩
    · intro i
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcompat i)).mono
        ((e i).symm.trans B).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
    · intro y hy
      have hyR := interior_subset hy.2
      exact ⟨fun hyS => (hlevel ⟨y, hyR⟩ hy.1).mp hyS.2,
        fun hz => ⟨hyR, (hlevel ⟨y, hyR⟩ hy.1).mpr hz⟩⟩
    · exact disjoint_interior_frontier.mono_left (fun _ hy => hy.2)

open Classical in
theorem HamiltonZeroThirdCoordinateRegularity.exists_original_circle_incidence
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {phi : C(H0, H0)} {theta : C0}
    (he : PLDomain e R) (hreg : HamiltonZeroThirdCoordinateRegularity e R phi theta) :
    let S := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {theta}
    ∃ (s : Finset (univ : Set X0)) (F : X0 → (s → ℝ × V3))
      (K B : SimplicialComplex ℝ (s → ℝ × V3)) (g : (s → ℝ × V3) → X0),
      Continuous F ∧ Function.Injective F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ B ≤ K ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ B.vertices) → t ∈ B.faces) ∧
      K.space = F '' S ∧ B.space = F '' (S ∩ frontier R) ∧
      PolyhedralPLInCharts e g K.space ∧ InjOn g K.space ∧
      (∀ z ∈ K.space, F (g z) = z) ∧ g '' K.space = S ∧
      (∀ t ∈ K.faces, ∃ q ∈ K.faces, q.card = 3 ∧ t ⊆ q) ∧
      (∀ t ∈ K.faces, t.card = 2 →
        {q : Finset (s → ℝ × V3) | q ∈ K.faces ∧ q.card = 3 ∧ t ⊆ q}.ncard =
          if t ∈ B.faces then 1 else 2) ∧
      (∀ v ∈ K.vertices, IsConnected (K.link v).space) ∧
      ∃ (m : ℕ) (J : Fin m → SimplicialComplex ℝ (s → ℝ × V3))
        (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space),
        (∀ i, J i ≤ B ∧ J i ≤ K ∧ (J i).faces.Finite ∧ (gamma i).IsFinitePL) ∧
        Pairwise (fun i j => Disjoint (J i).space (J j).space) ∧
        (⋃ i, (J i).space) = F '' (S ∩ frontier R) ∧
        ∀ t, t ∈ B.faces ↔ ∃ i, t ∈ (J i).faces := by
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hS : IsCompact (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {theta}) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset
      (he.closed.inter (isClosed_singleton.preimage (hamiltonZeroThirdCircleMap phi).continuous))
      (subset_univ _)
  exact exists_original_marked_surface_circle_incidence e isCompact_hamiltonZeroAmbient he hS
    hreg.exists_marked_surface_chart

end PoincareConjecture.M76
