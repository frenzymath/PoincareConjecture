import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.Pullback
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.FiniteCylinderDiskCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.Boundary.OriginalDiskParametrization
import PoincareConjecture.Proofs.M76.Rigidity.SourceMeridianBand

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_exact_proper_disk_of_original_cylindrical_band
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {N B : Set X}
    (he : PLDomain e N) (hN : IsCompact N)
    (c : (Q ×ˢ I) ≃ₜ B) (hB : B ⊆ frontier N)
    (q : V2 × ℝ → X) (hq : PolyhedralPLInCharts e q (Q ×ˢ I))
    (hcq : ∀ z : Q ×ˢ I, (c z : X) = q z)
    (j : V2 → X) (hj : PolyhedralPLInCharts e j D)
    (hji : Topology.IsEmbedding (fun z : D => j z)) (hjN : MapsTo j D N)
    (rim : C(Q, cylinderBandInterior c)) (hjr : ∀ z : Q, j z = (rim z : X))
    (hessential : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((Dehn.squareRimLoop.map rim.continuous).map
        (ContinuousMap.inclusion (cylinderBandInterior_subset c)).continuous)) ≠ 1) :
    ∃ j' : V2 → X, PolyhedralPLInCharts e j' D ∧
      Topology.IsEmbedding (fun z : D => j' z) ∧ MapsTo j' D N ∧
      (∀ z : D, j' z ∈ frontier N ↔ (z : V2) ∈ Q) ∧
      ∀ z : Q, j' z = (c ⟨((z : V2), 0), z.property, by norm_num⟩ : X) := by
  classical
  have hNne : N.Nonempty := ⟨j 0, hjN (mem_closedBall_self (by norm_num))⟩
  obtain ⟨M⟩ := he.nonempty_original_finite_collar_model hN hNne
  let V := M.vertices → ℝ × V3
  let fb : V2 × ℝ → V := M.coordinates ∘ q
  have hqN : MapsTo q (Q ×ˢ I) N := by
    intro z hz
    rw [← hcq ⟨z, hz⟩]
    exact he.closed.frontier_subset (hB (c ⟨z, hz⟩).property)
  obtain ⟨K, hK, hKs⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  have hfb : FinitePiecewiseAffineOn fb (Q ×ˢ I) := by
    have h := (hKs.symm ▸ hq).finitePiecewiseAffineOn_comp K hK M.coordinates_pl
    exact hKs ▸ h
  have hfbi : InjOn fb (Q ×ˢ I) := by
    intro x hx y hy hxy
    have hqxy := M.coordinates_injective (hqN hx) (hqN hy) hxy
    have hcxy : c ⟨x, hx⟩ = c ⟨y, hy⟩ :=
      Subtype.ext ((hcq ⟨x, hx⟩).trans (hqxy.trans (hcq ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (c.injective hcxy)
  obtain ⟨cM, hcM, hcMval⟩ := hfb.exists_homeomorph_image hfbi
  let T : Set V := fb '' (Q ×ˢ I)
  have hTB : T ⊆ M.boundary.space := by
    rintro _ ⟨z, hz, rfl⟩
    apply (M.coordinates_boundary _ (hqN hz)).mpr
    rw [← hcq ⟨z, hz⟩]
    exact hB (c ⟨z, hz⟩).property
  let b : B ≃ₜ T := c.symm.trans cM
  let rimB : C(Q, B) := (ContinuousMap.inclusion (cylinderBandInterior_subset c)).comp rim
  let rimM : C(Q, T) := (⟨b, b.continuous⟩ : C(B, T)).comp rimB
  have hrimM (z : Q) : (rimM z : V) = M.coordinates (rim z : X) := by
    change (cM (c.symm (rimB z)) : V) = _
    rw [hcMval]
    change M.coordinates (q (c.symm (rimB z))) = _
    rw [← hcq (c.symm (rimB z)), c.apply_symm_apply]
    rfl
  have hheight (z : Q) : (cM.symm (rimM z) : V2 × ℝ).2 ∈ Ioo (-1 : ℝ) 1 := by
    change (cM.symm (cM (c.symm (rimB z))) : V2 × ℝ).2 ∈ _
    rw [cM.symm_apply_apply]
    obtain ⟨w, hw, hweq⟩ := (rim z).property
    have hcw : c w = rimB z := Subtype.ext hweq
    rw [← hcw, c.symm_apply_apply]
    exact hw
  have hessentialM : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Dehn.squareRimLoop.map rimM.continuous)) ≠ 1 := by
    intro hnull
    let back : C(T, B) := ⟨b.symm, b.symm.continuous⟩
    have hback (z : Q) : back (rimM z) = rimB z := b.symm_apply_apply _
    have hhom := (Path.Homotopic.Quotient.eq.mp hnull).map back
    have hpath : ((Dehn.squareRimLoop.map rimM.continuous).map back.continuous).toContinuousMap =
        ((Dehn.squareRimLoop.map rim.continuous).map
          (ContinuousMap.inclusion (cylinderBandInterior_subset c)).continuous).toContinuousMap :=
      ContinuousMap.ext (fun t => hback (Dehn.squareRimLoop t))
    have hconst : ((Path.refl (rimM Dehn.squareRimBase)).map back.continuous).toContinuousMap =
        (Path.refl (rimB Dehn.squareRimBase)).toContinuousMap :=
      ContinuousMap.ext (fun _ => hback Dehn.squareRimBase)
    change ((Dehn.squareRimLoop.map rimM.continuous).map back.continuous).toContinuousMap.HomotopicRel
      ((Path.refl (rimM Dehn.squareRimBase)).map back.continuous).toContinuousMap {0, 1} at hhom
    rw [hpath, hconst] at hhom
    exact hessential (Path.Homotopic.Quotient.eq.mpr hhom)
  have hjM : FinitePiecewiseAffineOn (M.coordinates ∘ j) D := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJD, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 2)
    have h := (hJD.symm ▸ hj).finitePiecewiseAffineOn_comp J hJ M.coordinates_pl
    exact hJD ▸ h
  have hjiM : InjOn (M.coordinates ∘ j) D := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hji.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩)
      (M.coordinates_injective (hjN hx) (hjN hy) hxy))
  obtain ⟨D', S, gamma, hD, hDK, hfront, hgamma, hgamval⟩ :=
    M.exists_proper_disk_of_essential_cylindrical_rim cM hcM hTB
      (M.coordinates ∘ j) hjM hjiM (fun _ hz => M.coordinates_mapsTo (hjN hz))
      rimM (fun z => (congrArg M.coordinates (hjr z)).trans (hrimM z).symm)
      hessentialM hheight
  obtain ⟨j', hj', hji', hjN', hproper', hrim'⟩ := M.exists_exact_original_disk
    hD hDK hfront gamma hgamma (fun z => q (z, 0))
    (fun z hz => hqN ⟨hz, by norm_num⟩)
    (fun z => (hgamval z).trans (hcMval ⟨((z : V2), 0), z.property, by norm_num⟩))
  refine ⟨j', hj', hji', hjN', hproper', ?_⟩
  intro z
  exact (hrim' z z.property).trans (hcq ⟨((z : V2), 0), z.property, by norm_num⟩).symm

end PoincareConjecture.M76.HamiltonIntervalTorus
