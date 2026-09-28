import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.OriginalLift
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
noncomputable section
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => Set.prod (sphere (0 : V2) 1) (Icc (-(1/2 : ℝ)) (1/2))
local notation "Band" => Set.prod (sphere (0 : V2) 1) (Icc (-1 : ℝ) 1)

def halfBandScale : E →ᴬ[ℝ] E :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
    ((1/2 : ℝ) • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)

@[simp] theorem halfBandScale_apply (p : E) : halfBandScale p = (p.1,p.2/2) := by
  simp [halfBandScale,div_eq_mul_inv,mul_comm]

theorem halfBandScale_mem {p : E} : halfBandScale p ∈ Cyl ↔ p ∈ Band := by
  simp only [halfBandScale_apply]
  constructor <;> rintro ⟨hz,hs,ht⟩ <;> exact ⟨hz,by linarith,by linarith⟩

theorem corrected_cylinder_open_iff
    (H : Cyl ≃ₜ Cyl)
    (hends : ∀ p : Cyl, (p : E).2= -(1/2 : ℝ) ∨ (p : E).2=1/2 → H p=p)
    (p : Cyl) :
    (H p : E).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) ↔
      (p : E).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) := by
  constructor
  · intro hp
    have hlo : (p : E).2 ≠ -(1/2 : ℝ) := by
      intro hz
      rw [hends p (Or.inl hz),hz] at hp
      exact lt_irrefl _ hp.1
    have hhi : (p : E).2 ≠ 1/2 := by
      intro hz
      rw [hends p (Or.inr hz),hz] at hp
      exact lt_irrefl _ hp.2
    exact ⟨lt_of_le_of_ne p.property.2.1 (Ne.symm hlo),lt_of_le_of_ne p.property.2.2 hhi⟩
  · intro hp
    have hlo : (H p : E).2 ≠ -(1/2 : ℝ) := by
      intro hz
      have heq : H p=p := H.injective (hends (H p) (Or.inl hz))
      rw [heq] at hz
      exact (ne_of_gt hp.1) hz
    have hhi : (H p : E).2 ≠ 1/2 := by
      intro hz
      have heq : H p=p := H.injective (hends (H p) (Or.inr hz))
      rw [heq] at hz
      exact (ne_of_lt hp.2) hz
    exact ⟨lt_of_le_of_ne (H p).property.2.1 (Ne.symm hlo),
      lt_of_le_of_ne (H p).property.2.2 hhi⟩

theorem exists_full_original_band_of_cylinder_correction
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e Q j)
    (hopen : IsOpen ((Subtype.val : frontier Q → X) ⁻¹'
      (P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)))))
    (H : Cyl ≃ₜ Cyl) (hH : H.IsFinitePL)
    (hcore : ∀ z (hz : z ∈ Rim), H ⟨(z,0),hz,by norm_num⟩=⟨(z,0),hz,by norm_num⟩)
    (hends : ∀ p : Cyl, (p : E).2= -(1/2 : ℝ) ∨ (p : E).2=1/2 → H p=p) :
    ∃ F : E → X, PolyhedralPLInCharts e F Band ∧ InjOn F Band ∧
      MapsTo F Band (frontier Q) ∧ (∀ z ∈ Rim, F (z,0)=j z) ∧
      IsOpen ((Subtype.val : frontier Q → X) ⁻¹' (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))) ∧
      (∀ p (hp : p ∈ Band), F p=P.map (H ⟨halfBandScale p,halfBandScale_mem.mpr hp⟩)) := by
  obtain ⟨h,hh,hvalue⟩ := hH
  obtain ⟨K,hK,hKs⟩ := exists_finite_hamiltonMeridianBand (show (-1 : ℝ) < 1 by norm_num)
  have hscale : FinitePiecewiseAffineOn halfBandScale Band :=
    ⟨K,hK,hKs,K.affineOnFaces_affine halfBandScale⟩
  have hcoord := hh.comp hscale (fun _ hp => halfBandScale_mem.mpr hp)
  let F : E → X := P.map ∘ h ∘ halfBandScale
  have hformula (p : E) (hp : p ∈ Band) :
      F p=P.map (H ⟨halfBandScale p,halfBandScale_mem.mpr hp⟩) :=
    congrArg P.map (hvalue ⟨halfBandScale p,halfBandScale_mem.mpr hp⟩).symm
  have hfull : Cyl ⊆ Disk ×ˢ I := by
    intro p hp
    exact ⟨sphere_subset_closedBall hp.1,by linarith [hp.2.1],by linarith [hp.2.2]⟩
  have hcoordmap : MapsTo (h ∘ halfBandScale) Band (Disk ×ˢ I) := by
    intro p hp
    rw [Function.comp_apply,← hvalue ⟨halfBandScale p,halfBandScale_mem.mpr hp⟩]
    exact hfull (H _).property
  have hPL : PolyhedralPLInCharts e F Band := by
    have hh := P.polyhedral.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hcoord)
      (fun _ hp => hcoordmap (hKs.subset hp))
    rw [hKs] at hh
    change PolyhedralPLInCharts e F Band at hh
    exact hh
  have himage : F '' (Rim ×ˢ Ioo (-1 : ℝ) 1) =
      P.map '' (Rim ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := by
    apply Subset.antisymm
    · rintro y ⟨p,hp,rfl⟩
      have hpB : p ∈ Band := ⟨hp.1,Ioo_subset_Icc_self hp.2⟩
      let q : Cyl := ⟨halfBandScale p,halfBandScale_mem.mpr hpB⟩
      refine ⟨H q,⟨(H q).property.1,?_⟩,(hformula p hpB).symm⟩
      apply (corrected_cylinder_open_iff H hends q).mpr
      change (halfBandScale p).2 ∈ Ioo (-(1/2 : ℝ)) (1/2)
      rw [halfBandScale_apply]
      constructor <;> linarith [hp.2.1,hp.2.2]
    · rintro y ⟨q,hq,rfl⟩
      let q' : Cyl := ⟨q,hq.1,Ioo_subset_Icc_self hq.2⟩
      let p := H.symm q'
      have hp : (p : E).2 ∈ Ioo (-(1/2 : ℝ)) (1/2) :=
        (corrected_cylinder_open_iff H hends p).mp (by simpa [p] using hq.2)
      have hz : ((p : E).1,2*(p : E).2) ∈ Rim ×ˢ Ioo (-1 : ℝ) 1 :=
        ⟨p.property.1,by constructor <;> linarith [hp.1,hp.2]⟩
      refine ⟨((p : E).1,2*(p : E).2),hz,?_⟩
      rw [hformula _ ⟨hz.1,Ioo_subset_Icc_self hz.2⟩]
      have heq : (⟨halfBandScale ((p : E).1,2*(p : E).2),
          halfBandScale_mem.mpr ⟨hz.1,Ioo_subset_Icc_self hz.2⟩⟩ : Cyl)=p := by
        apply Subtype.ext
        simp
      rw [heq,H.apply_symm_apply]
  refine ⟨F,hPL,?_,?_,?_,by rwa [himage],hformula⟩
  · intro p hp q hq heq
    rw [hformula p hp,hformula q hq] at heq
    have hh := P.injective (hfull (H _).property) (hfull (H _).property) heq
    have hscaled := congrArg Subtype.val (H.injective (Subtype.ext hh))
    apply Prod.ext
    · simpa only [halfBandScale_apply] using congrArg Prod.fst hscaled
    · have ht := congrArg Prod.snd hscaled
      simp only [halfBandScale_apply] at ht
      linarith
  · intro p hp
    rw [hformula p hp]
    exact (P.proper _ (hfull (H _).property)).mpr (H _).property.1
  · intro z hz
    rw [hformula (z,0) ⟨hz,by norm_num⟩]
    have heq : (⟨halfBandScale (z,0),halfBandScale_mem.mpr ⟨hz,by norm_num⟩⟩ : Cyl)=
        ⟨(z,0),hz,by norm_num⟩ := by apply Subtype.ext; simp
    rw [heq,hcore z hz]
    exact P.central _ (sphere_subset_closedBall hz)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
