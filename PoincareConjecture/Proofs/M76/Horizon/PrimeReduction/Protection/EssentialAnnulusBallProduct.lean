import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskProtectedBallProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.Straightening








set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => (P2 × ℝ)
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Cube" => Set.prod Square (Icc (-1 : ℝ) 1)

theorem range_annulus_core_depth_zero :
    range Dehn.annulusCoreCircle = {z : Ann | depth 8 (z : P2) = 0} := by
  apply Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    rw [mem_ofPred_eq, Dehn.annulusCoreCircle_apply]
    exact depth_annulusMap (by norm_num) (by norm_num) z
  · intro x hx
    obtain ⟨s, _, hv⟩ := exists_period_parameter_of_depth (L := 8) (d := 1)
      (by norm_num) (by norm_num) x
    refine ⟨(s : Circle), Subtype.ext ?_⟩
    rw [Dehn.annulusCoreCircle_apply]
    simpa only [show depth 8 (x : P2) = 0 from hx] using hv.symm

theorem exists_annulus_parametrization_with_essential_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : Set E} (H : Ann ≃ₜ A) (hH : H.IsFinitePL)
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ H' : Ann ≃ₜ A, H'.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 → H' z = H z) ∧
      (fun z : Ann => (H' z : E)) '' {z | depth 8 (z : P2) = 0} =
        (fun z : Ann => (H z : E)) '' range gamma := by
  obtain ⟨G, hG, hGi, hfix, hrange, _⟩ :=
    Dehn.exists_finitePL_annular_straightening gamma hinj f hf hvalue hdepth hessential
  have hfixed (z : Ann) (hz : depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1) : G z = z := by
    rcases hz with hz | hz
    · obtain ⟨w, rfl⟩ := (Dehn.range_annulusRimPoint false).symm.subset hz
      exact hfix false w
    · obtain ⟨w, rfl⟩ := (Dehn.range_annulusRimPoint true).symm.subset hz
      exact hfix true w
  let H' := G.symm.trans H
  refine ⟨H', hGi.trans hH, ?_, ?_⟩
  · intro z hz
    change H (G.symm z) = H z
    apply congrArg H
    apply G.injective
    rw [G.apply_symm_apply, hfixed z hz]
  · have himage : G.symm '' {z : Ann | depth 8 (z : P2) = 0} = range gamma := by
      rw [← range_annulus_core_depth_zero, ← hrange, image_image]
      simp only [G.symm_apply_apply, image_id']
    change (fun z => (H (G.symm z) : E)) '' _ = _
    change ((fun z : Ann => (H z : E)) ∘ G.symm) '' _ = _
    rw [image_comp, himage]

theorem exists_cube_product_with_prescribed_disks_and_essential_meridian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q S J B : Set E} (hball : IsFinitePLBallPair V3 Q S)
    (d r : Bool → Set E) (hd : ∀ i, IsFinitePLBallPair P2 (d i) (r i))
    (hdS : ∀ i, d i ⊆ S) (hdis : Disjoint (d false) (d true))
    (hcover : d false ∪ d true = J) (hrcover : r false ∪ r true = B)
    (ann : Ann ≃ₜ (S \ (J \ B) : Set E)) (hann : ann.IsFinitePL)
    (hlo : ∀ z : Ann, depth 8 (z : P2) = -1 ↔ (ann z : E) ∈ r false)
    (hhi : ∀ z : Ann, depth 8 (z : P2) = 1 ↔ (ann z : E) ∈ r true)
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ G : Cube ≃ₜ Q, G.IsFinitePL ∧
      (∀ i (z : Cube), (G z : E) ∈ d i ↔ z.val.2 = if i then 1 else -1) ∧
      (∀ z : Cube, (G z : E) ∈ S ↔ z.val ∈ frontier Cube) ∧
      ∀ z : Cube, (G z : E) ∈ (fun w : Ann => (ann w : E)) '' range gamma ↔
        (|z.val.1.1| = 1 ∨ |z.val.1.2| = 1) ∧ z.val.2 = 0 := by
  obtain ⟨ann', hann', hkeep, hcore⟩ := exists_annulus_parametrization_with_essential_core
    ann hann gamma hinj f hf hvalue hdepth hessential
  have hmark (side : Bool) (z : Ann) :
      depth 8 (z : P2) = (if side then 1 else -1) ↔ (ann' z : E) ∈ r side := by
    have hold (w : Ann) : depth 8 (w : P2) = (if side then 1 else -1) ↔
        (ann w : E) ∈ r side := by cases side; exact hlo w; exact hhi w
    have hrim (w : Ann) (hw : depth 8 (w : P2) = (if side then 1 else -1)) :
        ann' w = ann w := by
      apply hkeep
      cases side
      · exact Or.inl hw
      · exact Or.inr hw
    constructor
    · intro hz
      rw [hrim z hz]
      exact (hold z).mp hz
    · intro hz
      let w := ann.symm (ann' z)
      have hv : ann w = ann' z := ann.apply_symm_apply _
      have hw : depth 8 (w : P2) = (if side then 1 else -1) :=
        (hold w).mpr (by rw [hv]; exact hz)
      have hwz : w = z := ann'.injective ((hrim w hw).trans hv)
      exact hwz ▸ hw
  obtain ⟨G, hG, hends, hfront, hlat, hheight⟩ :=
    exists_cube_product_with_prescribed_disks_with_height hball d r hd hdS hdis
      hcover hrcover ann' hann' (hmark false) (hmark true)
  refine ⟨G, hG, hends, hfront, ?_⟩
  intro z
  rw [← hcore]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hA : (G z : E) ∈ S \ (J \ B) := hwz ▸ (ann' w).property
    have heq : (⟨ann' w, hball.1 (ann' w).property.1⟩ : Q) = G z := Subtype.ext hwz
    have hh := hheight w
    rw [heq, G.symm_apply_apply] at hh
    exact ⟨(hlat z).mp hA, hh.trans hw⟩
  · rintro ⟨hzlat, hz0⟩
    have hA := (hlat z).mpr hzlat
    let w := ann'.symm ⟨G z, hA⟩
    have hw : (ann' w : E) = G z := congrArg Subtype.val (ann'.apply_symm_apply _)
    have heq : (⟨ann' w, hball.1 (ann' w).property.1⟩ : Q) = G z := Subtype.ext hw
    have hh := hheight w
    rw [heq, G.symm_apply_apply, hz0] at hh
    exact ⟨w, hh.symm, hw⟩

end PoincareConjecture.M76
