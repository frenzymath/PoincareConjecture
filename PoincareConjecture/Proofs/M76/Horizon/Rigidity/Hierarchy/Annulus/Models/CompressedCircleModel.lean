import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.MarkedCircleModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.RegularMarkedCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Compression.MarkedCharts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

open Classical in
theorem exists_hamiltonZero_compressed_marked_surface_chart
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other}))) :
    let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
    ∀ x ∈ S, ∃ T : OpenPartialHomeomorph X0 V3,
      x ∈ T.source ∧ (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      ((∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3), ell.contLinear v = 1 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0) ∧ Disjoint T.source (frontier R)) ∨
        ∃ (ell height : V3 →ᴬ[ℝ] ℝ) (u v : V3),
          height.contLinear u = 1 ∧ ell.contLinear v = 1 ∧ height.contLinear v = 0 ∧
          (∀ y ∈ T.source, y ∈ S ↔ ell (T y) = 0 ∧ 0 ≤ height (T y)) ∧
          ∀ y ∈ T.source, y ∈ frontier R ↔ height (T y) = 0) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hcompact (t : C0) : IsCompact (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {t}) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset
      (heR.closed.inter (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap psi).continuous))
      (subset_univ _)
  have hdis : Disjoint (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other}) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hne (hx.2.symm.trans hy.2)
  exact marked_surface_charts_after_interior_change hN isClosed_frontier
    (hcompact other).isClosed hfront hdis hA.isClosed
    (disjoint_interior_frontier.mono_left hAR)
    (S := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta})
    (by
      intro x hx
      have hq : hamiltonZeroSecondCircleMap psi x = hamiltonZeroSecondCircleMap phi x := by
        simp only [hamiltonZeroSecondCircleMap_ambient, hfixed x hx]
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hq])
    (by
      intro x hx
      obtain ⟨T, hxT, hcompat, hkind⟩ := hreg.exists_marked_surface_chart x hx.1
      rcases hkind with ⟨_, _, _, _, hdis⟩ | ⟨ell, height, u, v, hu, hv, huv, hS, hB⟩
      · exact (disjoint_left.mp hdis hxT hx.2).elim
      · exact ⟨T, ell, height, u, v, hxT, hcompat, hu, hv, huv, hS, hB⟩)

open Classical in
theorem exists_hamiltonZero_compressed_circle_incidence
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other}))) :
    let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}
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
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hcompact (t : C0) : IsCompact (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {t}) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset
      (heR.closed.inter (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap psi).continuous))
      (subset_univ _)
  have hlocal := exists_hamiltonZero_compressed_marked_surface_chart e phi psi heR
    hA hAR hfixed hne hreg hN hfront
  exact exists_original_marked_surface_circle_incidence e isCompact_hamiltonZeroAmbient
    heR (hcompact theta) hlocal

end PoincareConjecture.M76
