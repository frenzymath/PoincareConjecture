import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.OriginalCollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.DisplacementLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.HomotopyDisplacement

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def hamiltonZeroCollarTangentialMap
    (phi : C(H0, H0)) (J : SimplicialComplex ℝ E) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0) {e : ι → OpenPartialHomeomorph X0 V3}
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r)) :
    C(J.space, C0 × C0) :=
  ⟨fun x => (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1,
    continuous_fst.comp ((Q0).continuous.comp ((hamiltonZeroAmbientMap phi).continuous.comp
      (hc.continuousOn.comp_continuous
        (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.property, by constructor <;> linarith⟩))))⟩

open Classical in

noncomputable def hamiltonZeroCollarPhaseTarget
    (J : SimplicialComplex ℝ E) (g : C(J.space, C0 × C0)) (theta : C0) : E → X0 :=
  fun x => if h : x ∈ J.space then (Q0).symm (g ⟨x, h⟩, theta) else (Q0).symm (0, theta)

theorem ChartwisePLMap.exists_hamiltonZero_collar_phase_adjustment
    {κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {r : ℝ} (hr : 0 < r) (c : E × ℝ → X0)
    (hc : PolyhedralPLInCharts e c (J.space ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : J.space ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2))))
    (theta : C0) (hphase : ∀ x ∈ J.space, hamiltonZeroCircleMap phi (c (x, 0)) = theta)
    (g : C(J.space, C0 × C0))
    (H : (hamiltonZeroCollarTangentialMap phi J hr c hc).Homotopy g)
    (hg : PolyhedralPLInCharts d (hamiltonZeroCollarPhaseTarget J g theta) J.space) :
    ∃ (psi : C(H0, H0)) (C : Set X0),
      IsCompact C ∧ C ⊆ c '' (J.space ×ˢ Ioo (-(r / 2)) (r / 2)) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty (phi.HomotopyRel psi (hamiltonZeroAmbientEquiv '' C)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      (∀ x, x ∉ C → hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
      (∀ x : J.space, (Q0 (hamiltonZeroAmbientMap psi (c (x, 0)))).1 = g x) := by
  classical
  obtain ⟨W, hW⟩ := LinearTorus.exists_real_displacement_of_homotopy p H
  let w : E → ℝ × ℝ := fun x => if h : x ∈ J.space then W ⟨x, h⟩ else 0
  have hwval (x : J.space) : w x = W x := by
    simp only [w, dif_pos x.property]
  have hwc : ContinuousOn w J.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact W.continuous.congr (fun x => (hwval x).symm)
  have hwquot (x : J.space) : LinearTorus.quotientMap p (w x) =
      g x - (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 := by
    rw [hwval]
    exact hW x
  let v : E → V3 := fun x => ![(w x).1, (w x).2, 0]
  have hvc : ContinuousOn v J.space := by
    apply continuousOn_pi.mpr
    intro j
    fin_cases j
    · exact hwc.fst
    · exact hwc.snd
    · exact continuousOn_const
  have hc0 : PolyhedralPLInCharts e (fun x => c (x, 0)) J.space := by
    let a : E →ᴬ[ℝ] E × ℝ :=
      (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ) |>.toContinuousAffineMap
    exact hc.comp_finitePiecewiseAffineOn J hJ
      ((J.affineOnFaces_affine a).finitePiecewiseAffineOn hJ)
      (fun x hx => ⟨hx, by constructor <;> linarith⟩)
  have hsum (x : J.space) :
      ((Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1.1 + ((w x).1 : C0),
        (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1.2 + ((w x).2 : C0)) = g x := by
    change (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 +
      LinearTorus.quotientMap p (w x) = g x
    rw [hwquot]
    abel
  have hvPL : FinitePiecewiseAffineOn v J.space := by
    apply hd.finitePiecewiseAffineOn_displacement J hJ
      (hphi.polyhedralPL_hamiltonZeroAmbientMap_comp J hJ hc0) hg v hvc
    intro x hx
    apply (Q0).injective
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [hamiltonZeroCollarPhaseTarget, dif_pos hx, Homeomorph.apply_symm_apply]
    apply Prod.ext
    · exact hsum ⟨x, hx⟩
    · change (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).2 + ((0 : ℝ) : C0) = theta
      rw [AddCircle.coe_zero, add_zero, hamiltonZeroAmbientMap_circle, hphase x hx]
  have hwPL : FinitePiecewiseAffineOn w J.space := by
    let a : V3 →ᴬ[ℝ] ℝ × ℝ :=
      ((ContinuousLinearMap.proj (0 : Fin 3)).prod
        (ContinuousLinearMap.proj (1 : Fin 3))).toContinuousAffineMap
    exact (hvPL.postcomp a).congr (fun x hx => rfl)
  obtain ⟨psi, C, hC, hCU, hpsi, Hpsi, Fpsi, Hexterior, hnormal, hfixed, hbase⟩ :=
    hphi.exists_hamiltonZero_collar_tangential_adjustment hd F J hJ hr c hc hi hopen w hwPL
  refine ⟨psi, C, hC, hCU, hpsi, Hpsi, Fpsi, Hexterior, hnormal, hfixed, ?_⟩
  intro x
  exact (hbase x x.property).trans (hsum x)

end PoincareConjecture.M76
