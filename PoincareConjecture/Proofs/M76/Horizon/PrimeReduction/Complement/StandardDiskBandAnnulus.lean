import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_standard_disk_band_annulus :
    ∃ a : P2 → V2 × ℝ, FinitePiecewiseAffineOn a Annulus ∧
      InjOn a Annulus ∧ a '' Annulus = Q ×ˢ J ∧
      ∀ z ∈ Annulus, (a z).2 = depth 8 z / 2 := by
  let D := _root_.Dehn.annulusSquare 8 0
  have hD : IsFinitePLBallPair P2 D (frontier D) :=
    _root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  obtain ⟨F,hF,hFbd⟩ := hD.exists_cube_chart
    (ContinuousLinearEquiv.ofFinrankEq (by simp) : P2 ≃L[ℝ] V2)
  have hFq (x : D) : (x : P2) ∈ frontier D ↔ (F x : V2) ∈ Q := by
    simpa only [frontier_closedBall _ one_ne_zero] using hFbd x
  let e := F.restrictSubsets hD.1 sphere_subset_closedBall hFq
  obtain ⟨K,hK,hKq⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  have he : e.IsFinitePL :=
    hF.restrictSubsets_of_target hD.1 sphere_subset_closedBall hFq K hK hKq
  obtain ⟨d,hd,hdperiod⟩ := exists_square_product_band_annulus
  have hdheight (z : Annulus) : (d z : P2 × ℝ).2 = depth 8 z := by
    obtain ⟨s,hs,hsp⟩ := exists_period_parameter_of_depth
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) z
    let u : Icc (-1 : ℝ) 1 := ⟨depth 8 z,mem_squareAnnulus_iff_depth.mp z.property⟩
    have heq : (⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)),u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : Annulus) = z :=
      Subtype.ext hsp.symm
    have h := congrArg (fun w : P2 × ℝ => w.2) (hdperiod s hs u)
    rwa [heq] at h
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLI,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  have hid : (Homeomorph.refl (Icc (-1 : ℝ) 1)).IsFinitePL :=
    ⟨id,⟨L,hL,hLI,L.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,fun _ => rfl⟩
  let H := d.trans ((Homeomorph.Set.prod (frontier D) (Icc (-1 : ℝ) 1)).trans
    ((e.prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod Q (Icc (-1 : ℝ) 1)).symm))
  have hH : H.IsFinitePL := hd.trans (he.prod hid)
  obtain ⟨t,ht,htval⟩ := hH
  let A : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((1 / 2 : ℝ) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  let a := A ∘ t
  have hAval (z : V2 × ℝ) : A z = (z.1,z.2 / 2) := by
    simp [A,div_eq_mul_inv,mul_comm]
  have ha : FinitePiecewiseAffineOn a Annulus := ht.postcomp A
  have hti : InjOn t Annulus := by
    intro x hx y hy hxy
    have hsub : H ⟨x,hx⟩ = H ⟨y,hy⟩ :=
      Subtype.ext ((htval ⟨x,hx⟩).trans (hxy.trans (htval ⟨y,hy⟩).symm))
    exact congrArg Subtype.val (H.injective hsub)
  have hai : InjOn a Annulus := by
    intro x hx y hy hxy
    apply hti hx hy
    change A (t x) = A (t y) at hxy
    rw [hAval,hAval] at hxy
    apply Prod.ext
    · simpa only using congrArg (fun z : V2 × ℝ => z.1) hxy
    · have hh := congrArg Prod.snd hxy
      dsimp at hh
      linarith
  have himage : a '' Annulus = Q ×ˢ J := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change A (t x) ∈ _
      rw [hAval,← htval ⟨x,hx⟩]
      exact ⟨(H ⟨x,hx⟩).property.1,by linarith [(H ⟨x,hx⟩).property.2.1],
        by linarith [(H ⟨x,hx⟩).property.2.2]⟩
    · rintro ⟨x,u⟩ ⟨hx,hu⟩
      let z : Q ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨(x,2*u),hx,by linarith [hu.1],by linarith [hu.2]⟩
      refine ⟨H.symm z,(H.symm z).property,?_⟩
      change A (t (H.symm z)) = (x,u)
      rw [← htval (H.symm z),H.apply_symm_apply,hAval]
      dsimp [z]
      congr 1
      ring
  refine ⟨a,ha,hai,himage,?_⟩
  intro z hz
  change (A (t z)).2 = _
  rw [hAval,← htval ⟨z,hz⟩]
  change (d ⟨z,hz⟩ : P2 × ℝ).2 / 2 = _
  rw [hdheight]

end PoincareConjecture.M76
