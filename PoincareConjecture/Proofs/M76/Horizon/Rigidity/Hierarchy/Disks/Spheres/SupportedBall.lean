import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallPhaseHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedProductPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Compression.Homotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.ThirdCoordinateLifts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Target.AffineQuotient
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.DisplacementLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.PolyhedralPLSelection

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Vcoord" => ((Fin 0 ⊕ Fin 3) → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

noncomputable def hamiltonZeroTargetThirdPhaseRetraction (theta : ℝ) : C(X0, X0) :=
  ⟨fun y => (Q0).symm (((theta : C0), (Q0 y).1.2), (Q0 y).2),
    (Q0).symm.continuous.comp
      ((continuous_const.prodMk (Q0).continuous.fst.snd).prodMk (Q0).continuous.snd)⟩

theorem hamiltonZeroTargetThirdPhaseRetraction_coordinates (theta : ℝ) (y : X0) :
    Q0 (hamiltonZeroTargetThirdPhaseRetraction theta y) =
      (((theta : C0), (Q0 y).1.2), (Q0 y).2) :=
  (Q0).apply_symm_apply _

theorem StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetThirdPhaseRetraction
    {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (theta : ℝ) {Y : E → X0} {S : Set E} (hY : PolyhedralPLInCharts d Y S) :
    PolyhedralPLInCharts d (hamiltonZeroTargetThirdPhaseRetraction theta ∘ Y) S := by
  classical
  let m : Vcoord →L[ℝ] Vcoord := ContinuousLinearMap.pi fun j =>
    if j = Sum.inr (0 : Fin 3) then 0 else ContinuousLinearMap.proj j
  let v : Vcoord := fun j => if j = Sum.inr (0 : Fin 3) then theta else 0
  let a : Vcoord →ᴬ[ℝ] Vcoord := m.toContinuousAffineMap + ContinuousAffineMap.const ℝ Vcoord v
  apply hd.polyhedralPL_postcomp_quotient_affine
    (hamiltonZeroTargetThirdPhaseRetraction theta) a _ hY
  intro z
  apply (Q0).injective
  rw [hamiltonZeroTargetThirdPhaseRetraction_coordinates]
  change (((theta : C0), (z (Sum.inr 1) : C0)), (z (Sum.inr 2) : C0)) =
    ((((a z) (Sum.inr 0) : C0), ((a z) (Sum.inr 1) : C0)), ((a z) (Sum.inr 2) : C0))
  simp [a, m, v]

theorem ChartwisePLMap.exists_hamiltonZero_supported_ball_third_displacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {D S : Set X0} (b : ChartwisePLBall e D S) (theta : ℝ)
    (hphase : ∀ x ∈ S, hamiltonZeroThirdCircleMap phi x = (theta : C0)) :
    ∃ (l : C(D, ℝ)) (w : C(X0, ℝ)),
      (∀ x : D, (l x : C0) = hamiltonZeroThirdCircleMap phi x) ∧
      (∀ x : D, (x : X0) ∈ S → l x = theta) ∧
      (∀ x : D, w x = theta - l x) ∧
      (∀ x, x ∉ interior D → w x = 0) ∧
      ∀ i, LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : ContractibleSpace D := b.contractibleSpace
  let : LocallyPathConnectedSpace (closedBall (0 : V3) 1) :=
    (convex_closedBall (0 : V3) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace D :=
    b.parametrization.symm.isOpenEmbedding.locallyPathConnectedSpace
  let q : C(D, C0) := (hamiltonZeroThirdCircleMap phi).comp
    ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨l, hl, hlS⟩ := AddCircle.exists_lift_eq_on_connected_set p q
    b.isConnected_boundary_in_carrier theta (fun x hx => hphase x hx)
  change ∀ x : D, (l x : C0) = hamiltonZeroThirdCircleMap phi x at hl
  let win : C(Unit × D, ℝ) := ⟨fun z => theta - l z.2,
    continuous_const.sub (l.continuous.comp continuous_snd)⟩
  obtain ⟨W, hWin, hWout⟩ := ContinuousMap.exists_paste_of_eq_on_frontier
    b.isCompact.isClosed win (ContinuousMap.const (Unit × X0) 0) (by
      intro t x hx
      change theta - l x = 0
      rw [hlS x (b.frontier_eq ▸ hx), sub_self])
  let w : C(X0, ℝ) := ⟨fun x => W ((), x),
    W.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hwD (x : D) : w x = theta - l x := hWin () x
  have hwout (x : X0) (hx : x ∉ interior D) : w x = 0 := hWout () x hx
  let v : X0 → V3 := fun x j => if j = 0 then w x else 0
  have hvc : Continuous v := continuous_pi (fun j => by dsimp only [v]; split_ifs <;> fun_prop)
  let g : C(X0, X0) := ⟨fun x => hamiltonZeroTargetVectorTranslation
      (v x, hamiltonZeroAmbientMap phi x),
    hamiltonZeroTargetVectorTranslation.continuous.comp
      (hvc.prodMk (hamiltonZeroAmbientMap phi).continuous)⟩
  have hselect (x : X0) : g x = hamiltonZeroAmbientMap phi x ∨
      g x = hamiltonZeroTargetThirdPhaseRetraction theta (hamiltonZeroAmbientMap phi x) := by
    by_cases hx : x ∈ D
    · right
      apply (Q0).injective
      rw [hamiltonZeroTargetThirdPhaseRetraction_coordinates]
      change Q0 (hamiltonZeroTargetVectorTranslation (v x, hamiltonZeroAmbientMap phi x)) = _
      rw [hamiltonZeroTargetVectorTranslation_coordinates]
      have hsum : hamiltonZeroThirdCircleMap phi x + (w x : C0) = (theta : C0) := by
        rw [hwD ⟨x, hx⟩, ← hl ⟨x, hx⟩]
        simp
      rw [hamiltonZeroThirdCircleMap_ambient] at hsum
      simpa [v] using congrArg
        (fun t : C0 => ((t, (Q0 (hamiltonZeroAmbientMap phi x)).1.2),
          (Q0 (hamiltonZeroAmbientMap phi x)).2)) hsum
    · left
      have hvzero : v x = 0 := by
        ext j
        simp [v, hwout x (fun h => hx (interior_subset h))]
      change hamiltonZeroTargetVectorTranslation (v x, _) = _
      rw [hvzero, hamiltonZeroTargetVectorTranslation_zero]
  refine ⟨l, w, hl, hlS, hwD, hwout, ?_⟩
  intro i z hz
  obtain ⟨K, u, hK, hxK, hKt, _, _⟩ :=
    exists_hamiltonZeroThirdCircleMap_lift_in_compatible_chart e d hd phi hphi
      ((e i).symm z) (e i) (fun j => hphi.source_domain.compatible j i)
      ((e i).map_target hz)
  rw [(e i).right_inv hz] at hxK
  have hqPL : PolyhedralPLInCharts e (e i).symm K.space :=
    polyhedralPLInCharts_of_one_chart_inverse K hK
      ((K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V3)).finitePiecewiseAffineOn hK) i hKt
  have hY := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hqPL
  have hZ : PolyhedralPLInCharts d (fun y => g ((e i).symm y)) K.space :=
    hY.continuous_selection hd.domain.cover hd.domain.compatible K hK
      (hd.polyhedralPL_hamiltonZeroTargetThirdPhaseRetraction theta hY)
      (g.continuous.comp_continuousOn hqPL.continuousOn) (fun y _ => hselect _)
  have hvPL := hd.finitePiecewiseAffineOn_displacement K hK hY hZ
    (v ∘ (e i).symm) (hvc.comp_continuousOn hqPL.continuousOn) (fun _ _ => rfl)
  have hwPL : FinitePiecewiseAffineOn (w ∘ (e i).symm) K.space :=
    (hvPL.postcomp (ContinuousLinearMap.proj (0 : Fin 3)).toContinuousAffineMap).congr
      (fun _ _ => by simp [v])
  obtain ⟨J, hJ, hJK, hJPL⟩ := hwPL
  exact ⟨J, hJ, hJK ▸ hxK, hJK ▸ hKt, hJPL⟩

theorem ChartwisePLMap.exists_hamiltonZero_supported_ball_third_phase_homotopy
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {D S : Set X0} (b : ChartwisePLBall e D S) (theta : ℝ)
    (hphase : ∀ x ∈ S, hamiltonZeroThirdCircleMap phi x = (theta : C0)) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ x ∈ D, hamiltonZeroThirdCircleMap psi x = (theta : C0)) ∧
      (∀ c : C0, c ≠ (theta : C0) →
        (hamiltonZeroThirdCircleMap psi ⁻¹' {c}) =
          (hamiltonZeroThirdCircleMap phi ⁻¹' {c}) \ interior D) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior D)ᶜ,
        ∀ t x, (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x ∧
          (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x := by
  obtain ⟨l, w, hl, _, hwD, hwout, hwPL⟩ :=
    hphi.exists_hamiltonZero_supported_ball_third_displacement hd b theta hphase
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hq1, hq2, hq3, G, hG⟩ :=
    hphi.exists_hamiltonZero_third_scalar_homotopy hd F w hwPL hwout
  have hnew (x : X0) (hx : x ∈ D) :
      hamiltonZeroThirdCircleMap psi x = (theta : C0) := by
    rw [hq3, hwD ⟨x, hx⟩, ← hl ⟨x, hx⟩]
    simp
  refine ⟨psi, hpsi, Hpsi, Fpsi, hq1, hq2, hnew, ?_, G, ?_⟩
  · intro c hc
    ext x
    by_cases hx : x ∈ interior D
    · simp only [mem_preimage, mem_singleton_iff, hnew x (interior_subset hx),
        hc.symm, mem_sdiff, hx, not_true_eq_false, and_false]
    · change hamiltonZeroThirdCircleMap psi x = c ↔
        hamiltonZeroThirdCircleMap phi x = c ∧ x ∉ interior D
      rw [hq3, hwout x hx, AddCircle.coe_zero, add_zero]
      exact ⟨fun h => ⟨h, hx⟩, fun h => h.1⟩
  · intro t x
    rw [hG]
    exact ⟨rfl, rfl⟩

end PoincareConjecture.M76
