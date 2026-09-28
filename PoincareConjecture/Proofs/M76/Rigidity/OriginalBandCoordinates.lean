import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBandCarrier









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




theorem OriginalDiskProduct.exists_prescribed_band_coordinates
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (F : E → X) (hF : PolyhedralPLInCharts e F (Q ×ˢ I))
    (hFi : InjOn F (Q ×ˢ I)) (hfront : MapsTo F (Q ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Q, F (z, 0) = j z)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hband : MapsTo F (Q ×ˢ Icc (-a) a)
      (P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))) :
    ∃ k : X → E, ContinuousOn k (P.map '' (D ×ˢ I)) ∧
      (∀ z ∈ D ×ˢ I, k (P.map z) = z) ∧
      (∀ y ∈ P.map '' (D ×ˢ I), P.map (k y) = y) ∧
      MapsTo k (P.map '' (D ×ˢ I)) (D ×ˢ I) ∧
      FinitePiecewiseAffineOn (k ∘ F) (Q ×ˢ Icc (-a) a) ∧
      InjOn (k ∘ F) (Q ×ˢ Icc (-a) a) ∧
      MapsTo (k ∘ F) (Q ×ˢ Icc (-a) a) (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ z ∈ Q, k (F (z, 0)) = (z, 0)) ∧
      ∀ z ∈ Q ×ˢ Icc (-a) a, (k (F z)).2 = 0 ↔ z.2 = 0 := by
  obtain ⟨k, hkc, hleft, hback, hkmap⟩ := P.embedding.isEmbedding.exists_inverse_on_image
  have hfull : Q ×ˢ Icc (-a) a ⊆ Q ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hhalf : D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ D ×ˢ I := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hFP : MapsTo F (Q ×ˢ Icc (-a) a) (P.map '' (D ×ˢ I)) :=
    fun _ hz => image_mono hhalf (hband hz)
  have hq : ContinuousOn (k ∘ F) (Q ×ˢ Icc (-a) a) :=
    hkc.comp (hF.continuousOn.mono hfull) hFP
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand (by linarith : -a < a)
  have hqK : ContinuousOn (k ∘ F) K.space := hKS.symm ▸ hq
  have hqS : MapsTo (k ∘ F) K.space (D ×ˢ I) :=
    fun _ hz => hkmap (hFP (hKS.subset hz))
  have hFsmall := hF.restrict_finite K hK (hKS.subset.trans hfull)
  have hPq : PolyhedralPLInCharts e (P.map ∘ (k ∘ F)) K.space :=
    hFsmall.congr (fun z hz => (hback (F z) (hFP (hKS.subset hz))).symm)
  have hqPL := P.polyhedral.finitePiecewiseAffineOn_lift he.compatible P.injective
    K hK hqK hqS hPq
  rw [hKS] at hqPL
  have hcoord : MapsTo (k ∘ F) (Q ×ˢ Icc (-a) a)
      (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    obtain ⟨w, hw, hwF⟩ := hband hz
    change k (F z) ∈ _
    rw [← hwF, hleft w (hhalf hw)]
    exact ⟨(P.proper w (hhalf hw)).mp (hwF.symm ▸ hfront (hfull hz)), hw.2⟩
  have hzero (z : V2) (hz : z ∈ Q) : k (F (z, 0)) = (z, 0) := by
    rw [hcenter z hz, ← P.central z (sphere_subset_closedBall hz)]
    exact hleft (z, 0) ⟨sphere_subset_closedBall hz, by norm_num⟩
  refine ⟨k, hkc, hleft, hback, hkmap, hqPL, ?_, hcoord, hzero, ?_⟩
  · intro z hz w hw heq
    apply hFi (hfull hz) (hfull hw)
    exact (hback (F z) (hFP hz)).symm.trans
      ((congrArg P.map heq).trans (hback (F w) (hFP hw)))
  · intro z hz
    constructor
    · intro ht
      have hc := hcoord hz
      change k (F z) ∈ Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) at hc
      have hFc : F ((k (F z)).1, 0) = F z := by
        rw [hcenter _ hc.1, ← P.central _ (sphere_subset_closedBall hc.1)]
        have hp : ((k (F z)).1, (0 : ℝ)) = k (F z) := Prod.ext rfl ht.symm
        rw [hp]
        exact hback (F z) (hFP hz)
      have heq := hFi
        (show ((k (F z)).1, (0 : ℝ)) ∈ Q ×ˢ I from ⟨hc.1, by norm_num⟩)
        (hfull hz) hFc
      exact (congrArg Prod.snd heq).symm
    · intro ht
      have hz0 : z = (z.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [hz0, hzero z.1 hz.1]

end PoincareConjecture.M76
