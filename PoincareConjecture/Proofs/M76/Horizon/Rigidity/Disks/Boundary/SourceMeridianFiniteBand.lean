import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteCollarModel
import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianBand
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.SourceMeridianBandDisk
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_source_meridian_finite_band_disk
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (he : PLDomain e R) (M : OriginalFiniteCollarModel e R)
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    ∃ (T : Set (M.vertices → ℝ × V3)) (c : (Q ×ˢ I) ≃ₜ T)
      (j : V2 → (M.vertices → ℝ × V3)) (rim : C(Q, T)),
      T ⊆ M.boundary.space ∧ c.IsFinitePL ∧
      (∀ z : Q ×ˢ I, (c z : M.vertices → ℝ × V3) =
        M.coordinates (hamiltonMeridianCutAmbientMap z)) ∧
      FinitePiecewiseAffineOn j D ∧ InjOn j D ∧ MapsTo j D M.complex.space ∧
      (∀ z : Q, j z = (rim z : M.vertices → ℝ × V3)) ∧
      (∀ z : D, j z ∈ M.boundary.space ↔ (z : V2) ∈ Q) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 ∧
      (∀ z : Q, (c.symm (rim z) : V2 × ℝ).2 ∈ Ioo (-1 : ℝ) 1) := by
  classical
  let E := M.vertices → ℝ × V3
  let fb : V2 × ℝ → E := M.coordinates ∘ hamiltonMeridianCutAmbientMap
  have hbandR : MapsTo hamiltonMeridianCutAmbientMap (Q ×ˢ I) R :=
    fun _ hz => he.closed.frontier_subset (mapsTo_hamiltonMeridianBand_frontier hz)
  obtain ⟨K, hK, hKs⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  have hbandPL := polyhedralPL_source_hamiltonMeridianBand hd phi hphi F
  have hfb : FinitePiecewiseAffineOn fb (Q ×ˢ I) := by
    have h := (hKs.symm ▸ hbandPL).finitePiecewiseAffineOn_comp K hK M.coordinates_pl
    exact hKs ▸ h
  have hfbi : InjOn fb (Q ×ˢ I) := by
    intro x hx y hy hxy
    exact injOn_hamiltonMeridianBand hx hy
      (M.coordinates_injective (hbandR hx) (hbandR hy) hxy)
  obtain ⟨c, hc, hcval⟩ := hfb.exists_homeomorph_image hfbi
  let T : Set E := fb '' (Q ×ˢ I)
  have hTB : T ⊆ M.boundary.space := by
    rintro _ ⟨z, hz, rfl⟩
    exact (M.coordinates_boundary _ (hbandR hz)).mpr
      (mapsTo_hamiltonMeridianBand_frontier hz)
  obtain ⟨j, rim, hj, hji, hjR, hjrim, hjproper, hessential⟩ :=
    exists_source_meridian_open_band_disk e he
  have hrimR (z : Q) : (rim z : X) ∈ R :=
    he.closed.frontier_subset (hamiltonMeridianOpenBand_subset_frontier (rim z).property)
  have hrimT (z : Q) : M.coordinates (rim z : X) ∈ T := by
    obtain ⟨w, hw, hweq⟩ := (rim z).property
    exact ⟨w, ⟨hw.1, hw.2.1.le, hw.2.2.le⟩, congrArg M.coordinates hweq⟩
  let rimM : C(Q, T) :=
    ⟨fun z => ⟨M.coordinates (rim z : X), hrimT z⟩,
      (M.coordinates_continuous.comp
        (continuous_subtype_val.comp rim.continuous)).subtype_mk hrimT⟩
  have hlift (z : Q) :
      hamiltonMeridianCutAmbientMap (c.symm (rimM z)) = (rim z : X) := by
    apply M.coordinates_injective (hbandR (c.symm (rimM z)).property) (hrimR z)
    exact (hcval (c.symm (rimM z))).symm.trans
      (congrArg Subtype.val (c.apply_symm_apply (rimM z)))
  have hstrict (z : Q) : (c.symm (rimM z) : V2 × ℝ).2 ∈ Ioo (-1 : ℝ) 1 := by
    obtain ⟨w, hw, hweq⟩ := (rim z).property
    have heq := injOn_hamiltonMeridianBand (c.symm (rimM z)).property
      ⟨hw.1, hw.2.1.le, hw.2.2.le⟩ ((hlift z).trans hweq.symm)
    exact congrArg Prod.snd heq ▸ hw.2
  let project : C(T, Q) :=
    ⟨fun y => ⟨(c.symm y : V2 × ℝ).1, (c.symm y).property.1⟩,
      (continuous_fst.comp (continuous_subtype_val.comp c.symm.continuous)).subtype_mk _⟩
  have hproject (z : Q) : project (rimM z) = hamiltonMeridianOpenBandProjection (rim z) :=
    Subtype.ext (congrArg Prod.fst (hlift z))
  have hessentialM : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map rimM.continuous)) ≠ 1 := by
    intro hclass
    have hnull : (Dehn.squareRimLoop.map rimM.continuous).Homotopic
        (Path.refl (rimM Dehn.squareRimBase)) := Path.Homotopic.Quotient.eq.mp hclass
    have hmapped := hnull.map project
    have hpath : ((Dehn.squareRimLoop.map rimM.continuous).map project.continuous).toContinuousMap =
        ((Dehn.squareRimLoop.map rim.continuous).map
          hamiltonMeridianOpenBandProjection.continuous).toContinuousMap :=
      ContinuousMap.ext (fun t => hproject (Dehn.squareRimLoop t))
    have hconst : ((Path.refl (rimM Dehn.squareRimBase)).map project.continuous).toContinuousMap =
        (Path.refl (hamiltonMeridianOpenBandProjection (rim Dehn.squareRimBase))).toContinuousMap :=
      ContinuousMap.ext (fun _ => hproject Dehn.squareRimBase)
    change ((Dehn.squareRimLoop.map rimM.continuous).map project.continuous).toContinuousMap.HomotopicRel
      ((Path.refl (rimM Dehn.squareRimBase)).map project.continuous).toContinuousMap {0, 1} at hmapped
    rw [hpath, hconst] at hmapped
    exact hessential (Path.Homotopic.Quotient.eq.mpr hmapped)
  have hjM : FinitePiecewiseAffineOn (M.coordinates ∘ j) D := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJD, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 2)
    have h := (hJD.symm ▸ hj).finitePiecewiseAffineOn_comp J hJ M.coordinates_pl
    exact hJD ▸ h
  refine ⟨T, c, M.coordinates ∘ j, rimM, hTB, hc, hcval, hjM, ?_,
    fun _ hz => M.coordinates_mapsTo (hjR hz), ?_, ?_, hessentialM, hstrict⟩
  · intro x hx y hy hxy
    exact congrArg Subtype.val (hji.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩)
      (M.coordinates_injective (hjR hx) (hjR hy) hxy))
  · intro z
    exact congrArg M.coordinates (hjrim z)
  · intro z
    exact (M.coordinates_boundary _ (hjR z.property)).trans (hjproper z)

end PoincareConjecture.M76
