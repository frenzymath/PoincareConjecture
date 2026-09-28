import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SquareCircle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift









set_option autoImplicit false
open Set Geometry Metric PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Rect" => rectangle (4 * (8 : ℝ)) 1
local notation "Square" => _root_.Dehn.annulusSquare 8 0



theorem exists_source_square_annulus_coordinates :
    ∃ (j : Circle ≃ₜ Q2) (H : source ≃ₜ Ann),
      FinitePiecewiseAffineOn
        (fun s : ℝ ↦ (j ((32 * s : ℝ) : Circle) : V2)) (Icc 0 1) ∧
      H.IsFinitePL ∧ H.symm.IsFinitePL ∧
      (∀ b z, H ⟨(endpoint b, j z),
        sphere_subset_closedBall (endpoint_mem_sphere b), (j z).property⟩ =
          annulusRimPoint b z) ∧
      ∀ b z, (H.symm (annulusRimPoint b z) : V1 × V2) = (endpoint b, (j z : V2)) := by
  classical
  obtain ⟨j, f, hf, hj, hjPL⟩ := exists_square_circle_coordinates
  let φ : P2 → V1 × V2 := fun p ↦ ((fun _ ↦ p.2), f (wrappedStripMap 8 (p.1, 0)))
  have hφvalue (s : ℝ) (hs : s ∈ Icc 0 (4 * (8 : ℝ))) (u : ℝ) :
      φ (s, u) = ((fun _ ↦ u), (j (s : Circle) : V2)) := by
    refine Prod.ext rfl ?_
    exact ((congrArg f (annulusMap_coe (L := 8) (t := 0)
      (by norm_num) (by norm_num) hs)).symm).trans (hj _).symm
  have hraw := finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨K, hK, hKs, hKraw⟩ := hraw
  let project : P2 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ P2 0)
  have hproject : FinitePiecewiseAffineOn project Rect :=
    ⟨K, hK, hKs, K.affineOnFaces_affine project⟩
  have hrawzero : FinitePiecewiseAffineOn (wrappedStripMap 8 ∘ project) Rect :=
    (show FinitePiecewiseAffineOn (wrappedStripMap 8) Rect from ⟨K, hK, hKs, hKraw⟩).comp
      hproject (fun p hp ↦ ⟨hp.1, by norm_num [project]⟩)
  have hmap : MapsTo (wrappedStripMap 8 ∘ project) Rect Square := by
    intro p hp
    change wrappedStripMap 8 (p.1, 0) ∈ Square
    rw [← annulusMap_coe (L := 8) (t := 0) (by norm_num) (by norm_num) hp.1]
    apply (_root_.Dehn.mem_annulusSquare_iff 8 0 _).mpr
    rw [depth_annulusMap (by norm_num) (by norm_num)]
  let first : P2 →ᴬ[ℝ] V1 :=
    (ContinuousLinearMap.pi (fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ ℝ ℝ)).toContinuousAffineMap
  have hfirst : FinitePiecewiseAffineOn first Rect :=
    ⟨K, hK, hKs, K.affineOnFaces_affine first⟩
  have hφ : FinitePiecewiseAffineOn φ Rect := hfirst.prod_mk (hf.comp hrawzero hmap)
  have hfib : ∀ x ∈ Rect, ∀ y ∈ Rect, φ x = φ y ↔ x.2 = y.2 ∧
      (x.1 : Circle) = (y.1 : Circle) := by
    intro x hx y hy
    rw [hφvalue x.1 hx.1 x.2, hφvalue y.1 hy.1 y.2]
    constructor
    · intro h
      exact ⟨congrArg (fun p : V1 × V2 ↦ p.1 0) h,
        j.injective (Subtype.ext (congrArg Prod.snd h))⟩
    · rintro ⟨hu, hs⟩
      rw [hu, hs]
  have himage : φ '' Rect = source := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [hφvalue p.1 hp.1 p.2]
      refine ⟨?_, (j (p.1 : Circle)).property⟩
      rw [mem_closedBall, dist_zero_right, pi_norm_const, Real.norm_eq_abs]
      exact abs_le.mpr hp.2
    · intro hy
      let z := j.symm ⟨y.2, hy.2⟩
      let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
      let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
      have hs : s ∈ Icc 0 (4 * (8 : ℝ)) :=
        ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.1,
          by simpa only [zero_add] using
            (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
      have hsz : (s : Circle) = z := AddCircle.coe_equivIco
      have hu : y.1 0 ∈ Icc (-1 : ℝ) 1 :=
        abs_le.mp ((norm_le_pi_norm y.1 0).trans (mem_closedBall_zero_iff.mp hy.1))
      refine ⟨(s, y.1 0), ⟨hs, hu⟩, ?_⟩
      rw [hφvalue s hs, hsz]
      apply Prod.ext
      · funext k
        exact congrArg y.1 (Subsingleton.elim 0 k)
      · exact congrArg Subtype.val (j.apply_symm_apply ⟨y.2, hy.2⟩)
  obtain ⟨c, hc, _, hcperiod, _⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
      (L := 8) (d := 1) (by norm_num) (by norm_num) φ hφ hfib
  let G := c.trans (Homeomorph.setCongr himage)
  have hGPL : G.IsFinitePL := hc.setCongr rfl himage
  have hG (b : Bool) (z : Circle) :
      (G (annulusRimPoint b z) : V1 × V2) = (endpoint b, (j z : V2)) := by
    let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
    let s : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
    have hs : s ∈ Icc 0 (4 * (8 : ℝ)) :=
      ⟨(AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.1,
        by simpa only [zero_add] using
          (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property.2.le⟩
    have hsz : (s : Circle) = z := AddCircle.coe_equivIco
    have hv := hcperiod s hs ⟨if b then 1 else -1, by cases b <;> norm_num⟩
    rw [hφvalue s hs, hsz] at hv
    exact hv
  refine ⟨j, G.symm, hjPL, hGPL.symm, hGPL, ?_, hG⟩
  intro b z
  apply G.injective
  rw [G.apply_symm_apply]
  exact Subtype.ext (hG b z).symm

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
