import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRetainedDisks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Half" => Icc (-(1 / 2) : ℝ) (1 / 2)
local notation "Square" => _root_.Dehn.annulusSquare 8 0
local notation "Annulus" => squareAnnulus 8 1

private theorem exists_half_width_product_annulus :
    ∃ c : Annulus ≃ₜ (Rim ×ˢ Half : Set (V2 × ℝ)),
      c.IsFinitePL ∧ ∀ p : Annulus, (c p : V2 × ℝ).2 = depth 8 p / 2 := by
  classical
  have hS := _root_.Dehn.isFinitePLBallPair_annulusSquare
    (L := 8) (u := 0) (by norm_num)
  obtain ⟨e, he, heb⟩ := hS.exists_cube_chart (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have heb' (x : Square) : (x : P2) ∈ frontier Square ↔ (e x : V2) ∈ Rim := by
    simpa only [frontier_closedBall _ one_ne_zero] using heb x
  let q := e.restrictSubsets hS.1 sphere_subset_closedBall heb'
  obtain ⟨_, K, _, _, hK, hKs⟩ := hS.exists_finite_carrier_and_rim_complexes
  have hq : q.IsFinitePL := he.restrictSubsets hS.1 sphere_subset_closedBall heb' K hK hKs
  obtain ⟨a, ha, hqa⟩ := hq
  obtain ⟨L, _, hL, hLs, _, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).exists_finite_carrier_and_rim_complexes
  let scale : ℝ →ᴬ[ℝ] ℝ := (1 / 2 : ℝ) • ContinuousAffineMap.id ℝ ℝ
  have hs : FinitePiecewiseAffineOn scale I :=
    ⟨L, hL, hLs, L.affineOnFaces_affine scale⟩
  let m := Prod.map a scale
  have hm : FinitePiecewiseAffineOn m (frontier Square ×ˢ I) := ha.prodMap hs
  have hmv (z : P2 × ℝ) : m z = (a z.1, z.2 / 2) := by
    change (a z.1, (1 / 2 : ℝ) * z.2) = (a z.1, z.2 / 2)
    congr 1
    ring
  have hmi : InjOn m (frontier Square ×ˢ I) := by
    intro x hx y hy hxy
    rw [hmv, hmv] at hxy
    apply Prod.ext
    · have hval : q ⟨x.1, hx.1⟩ = q ⟨y.1, hy.1⟩ := by
        apply Subtype.ext
        simpa only [hqa] using congrArg Prod.fst hxy
      exact congrArg Subtype.val (q.injective hval)
    · have h := congrArg Prod.snd hxy
      dsimp at h
      linarith
  have himage : m '' (frontier Square ×ˢ I) = Rim ×ˢ Half := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hmv, ← hqa ⟨z.1, hz.1⟩]
      exact ⟨(q ⟨z.1, hz.1⟩).property,
        by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    · intro z hz
      refine ⟨((q.symm ⟨z.1, hz.1⟩ : P2), 2 * z.2),
        ⟨(q.symm ⟨z.1, hz.1⟩).property, ?_⟩, ?_⟩
      · constructor <;> linarith [hz.2.1, hz.2.2]
      · rw [hmv, ← hqa, q.apply_symm_apply]
        simp
  obtain ⟨d, hd, hdval⟩ := hm.exists_homeomorph_image hmi
  obtain ⟨c, hc, hcperiod⟩ := exists_square_product_band_annulus
  let H := c.trans (d.trans (Homeomorph.setCongr himage))
  have hH : H.IsFinitePL := hc.trans (hd.setCongr rfl himage)
  refine ⟨H, hH, ?_⟩
  intro p
  have hheight : (c p : P2 × ℝ).2 = depth 8 p := by
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) p
    let u : I := ⟨depth 8 p, mem_squareAnnulus_iff_depth.mp p.property⟩
    have heq : (⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : Annulus) = p :=
      Subtype.ext hsp.symm
    have h := congrArg (fun z : P2 × ℝ => z.2) (hcperiod s hs u)
    rwa [heq] at h
  change (d (c p) : V2 × ℝ).2 = _
  rw [hdval, hmv, hheight]

theorem exists_proper_product_boundary_disks
    (f : V2 × ℝ → V3) (hf : FinitePiecewiseAffineOn f (Disk ×ˢ I))
    (hfi : InjOn f (Disk ×ˢ I))
    (hproper : ∀ z ∈ Disk ×ˢ I, f z ∈ Sphere ↔ z.1 ∈ Rim) :
    ∃ k : Bool → Set V3,
      (∀ b, IsFinitePLBallPair P2 (k b)
          (f '' (Rim ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)})) ∧
        k b ⊆ Sphere ∧ k b ∩ f '' (Rim ×ˢ Half) =
          f '' (Rim ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)})) ∧
      Disjoint (k true) (k false) ∧
      (k true ∪ k false) ∪ f '' (Rim ×ˢ Half) = Sphere := by
  classical
  have hsub : Rim ×ˢ Half ⊆ Disk ×ˢ I := by
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1,
      by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨L, _, hL, hLs, _, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (-(1 / 2) : ℝ) < 1 / 2)).exists_finite_carrier_and_rim_complexes
  obtain ⟨J, hJ, hJs, _⟩ := K.exists_finite_triangulation_prod L hK hL
  rw [hKs, hLs] at hJs
  have hband : FinitePiecewiseAffineOn f (Rim ×ˢ Half) :=
    hJs ▸ hf.restrict J hJ (hJs.subset.trans hsub)
  obtain ⟨d, hd, hdval⟩ := hband.exists_homeomorph_image (hfi.mono hsub)
  obtain ⟨c, hc, hheight⟩ := exists_half_width_product_annulus
  let H := c.trans d
  have hH : H.IsFinitePL := hc.trans hd
  have hHv (p : Annulus) : (H p : V3) = f (c p) := hdval (c p)
  have hrim (b : Bool) :
      (fun p : Annulus => (H p : V3)) '' {p | depth 8 p = if b then 1 else -1} =
        f '' (Rim ×ˢ {if b then (1 / 2 : ℝ) else -(1 / 2)}) := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨c p, ⟨(c p).property.1, ?_⟩, (hHv p).symm⟩
      rw [mem_singleton_iff, hheight, hp]
      cases b <;> norm_num
    · rintro _ ⟨z, hz, rfl⟩
      have hzhalf : z ∈ Rim ×ˢ Half := by
        refine ⟨hz.1, ?_⟩
        have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
        rw [ht]
        cases b <;> norm_num
      let p := c.symm ⟨z, hzhalf⟩
      have hcp : (c p : V2 × ℝ) = z := congrArg Subtype.val (c.apply_symm_apply _)
      refine ⟨p, ?_, ?_⟩
      · have hh := hheight p
        rw [hcp] at hh
        have ht : z.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hz.2
        change depth 8 p = _
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢ <;> linarith
      · change (H p : V3) = f z
        rw [hHv, hcp]
  have hBS : f '' (Rim ×ˢ Half) ⊆ Sphere := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hproper z (hsub hz)).mpr hz.1
  have hone : (1 : V2) ∈ Rim := by simp
  have hout : ((1 : V2), (3 / 4 : ℝ)) ∈ Disk ×ˢ I :=
    ⟨sphere_subset_closedBall hone, by norm_num⟩
  let p : Sphere := ⟨f ((1 : V2), 3 / 4), (hproper _ hout).mpr hone⟩
  have hp : (p : V3) ∉ f '' (Rim ×ˢ Half) := by
    rintro ⟨z, hz, heq⟩
    have hh := congrArg Prod.snd (hfi (hsub hz) hout heq)
    dsimp at hh
    linarith [hz.2.2]
  obtain ⟨k, hk, hdis, hwhole⟩ :=
    exists_unitCube_sphere_annulus_retained_disks H hH hBS p hp
  refine ⟨k, ?_, hdis, hwhole⟩
  intro b
  simpa only [hrim b] using hk b

end PoincareConjecture.M76
