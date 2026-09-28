import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.FiniteModelCollarTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalDiskLateralOwner
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem exists_finite_model_annulus_coordinates
    {X ι G : Type*} [TopologicalSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {e : ι → OpenPartialHomeomorph X V3} {R N : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (F : X → G)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F N) (hPN : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) N) :
    ∃ H : (F '' (P.map '' (Rim ×ˢ J))) ≃ₜ
        ((F '' (P.map '' (Rim ×ˢ {-(1/2 : ℝ)}))) ×ˢ I : Set (G × ℝ)),
      H.IsFinitePL ∧
      ∀ (b : Bool) (x : F '' (P.map '' (Rim ×ˢ J))),
        (x : G) ∈ F '' (P.map '' (Rim ×ˢ {if b then (1/2 : ℝ) else -(1/2)})) ↔
          (H x : G × ℝ) ∈
            (F '' (P.map '' (Rim ×ˢ {-(1/2 : ℝ)}))) ×ˢ {if b then (1 : ℝ) else 0} := by
  obtain ⟨K,hK,hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨KI,hKI,hKIs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L,hL,hLs,_⟩ := K.exists_finite_triangulation_prod KI hK hKI
  rw [hKIs] at hLs
  let A : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      ((ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap -
        ContinuousAffineMap.const ℝ (V2 × ℝ) (1/2))
  have hAval (z : V2 × ℝ) : A z = (z.1,z.2-1/2) := rfl
  let c := P.map ∘ A
  have hfull (z : V2 × ℝ) (hz : z ∈ K.space ×ˢ I) :
      A z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rw [hAval]
    exact ⟨sphere_subset_closedBall (hKs.subset hz.1),
      by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hc : PolyhedralPLInCharts e c (K.space ×ˢ I) := by
    rw [←hLs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn L hL
      ⟨L,hL,rfl,L.affineOnFaces_affine A⟩
      (fun z hz => hfull z (hLs.subset hz))
  have hci : InjOn c (K.space ×ˢ I) := by
    intro z hz w hw hzw
    have hh := P.injective (hfull z hz) (hfull w hw) hzw
    rw [hAval,hAval] at hh
    injection hh with hfst hsnd
    exact Prod.ext hfst (by linarith)
  obtain ⟨D,hD,_,hDval,_⟩ := exists_finite_model_boundary_product K hK c hc hci
    (fun z hz => hPN (hfull z hz)) F hF hFi
  have hbase : (fun x => F (c (x,0))) '' K.space =
      F '' (P.map '' (Rim ×ˢ {-(1/2 : ℝ)})) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨P.map (x,-(1/2)),⟨(x,-(1/2)),⟨hKs.subset hx,rfl⟩,rfl⟩,?_⟩
      simp [c,hAval]
    · rintro ⟨_,⟨⟨x,t⟩,⟨hx,ht⟩,rfl⟩,rfl⟩
      change t = -(1/2 : ℝ) at ht
      subst t
      refine ⟨x,hKs.symm.subset hx,?_⟩
      simp [c,hAval]
  have htarget : (F ∘ c) '' (K.space ×ˢ I) = F '' (P.map '' (Rim ×ˢ J)) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨P.map (A z),⟨A z,?_,rfl⟩,rfl⟩
      rw [hAval]
      exact ⟨hKs.subset hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨(z.1,z.2+1/2),⟨hKs.symm.subset hz.1,
        by linarith [hz.2.1],by linarith [hz.2.2]⟩,?_⟩
      change F (P.map (A (z.1,z.2+1/2))) = F (P.map z)
      rw [hAval]
      simp
  let H := (Homeomorph.setCongr htarget.symm).trans
    (D.symm.trans (Homeomorph.setCongr (congrArg (fun Z => Z ×ˢ I) hbase)))
  have hH : H.IsFinitePL := hD.symm.setCongr htarget
    (congrArg (fun Z => Z ×ˢ I) hbase)
  have hHval (z : V2 × ℝ) (hz : z ∈ Rim ×ˢ J) :
      (H ⟨F (P.map z),⟨P.map z,⟨z,hz,rfl⟩,rfl⟩⟩ : G × ℝ).2 = z.2+1/2 := by
    let x : K.space := ⟨z.1,hKs.symm.subset hz.1⟩
    let t : I := ⟨z.2+1/2,by linarith [hz.2.1],by linarith [hz.2.2]⟩
    have hv := hDval x t
    have heq : c ((x : V2),(t : ℝ)) = P.map z := by
      change P.map (A (z.1,z.2+1/2)) = P.map z
      rw [hAval]
      simp
    rw [heq] at hv
    let u : ((fun x => F (c (x,0))) '' K.space) ×ˢ I :=
      ⟨(F (c ((x : V2),0)),(t : ℝ)),⟨mem_image_of_mem _ x.property,t.property⟩⟩
    let y : (F ∘ c) '' (K.space ×ˢ I) :=
      ⟨F (P.map z),htarget.symm.subset ⟨P.map z,⟨z,hz,rfl⟩,rfl⟩⟩
    have huv : D u = y := Subtype.ext hv
    have hpre : D.symm y = u := by rw [←huv,D.symm_apply_apply]
    change (D.symm y : G × ℝ).2 = z.2+1/2
    rw [hpre]
  refine ⟨H,hH,?_⟩
  intro b ⟨x,hx⟩
  obtain ⟨_,⟨z,hz,rfl⟩,rfl⟩ := hx
  have hzfull : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨sphere_subset_closedBall hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hmem : F (P.map z) ∈
      F '' (P.map '' (Rim ×ˢ {if b then (1/2 : ℝ) else -(1/2)})) ↔
      z.2 = if b then (1/2 : ℝ) else -(1/2) := by
    constructor
    · rintro ⟨_,⟨w,hw,rfl⟩,hwz⟩
      have hwfull : w ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
        refine ⟨sphere_subset_closedBall hw.1,?_⟩
        have hwt : w.2 = if b then (1/2 : ℝ) else -(1/2) := hw.2
        rw [hwt]
        cases b <;> norm_num
      have hzw := P.injective hwfull hzfull (hFi (hPN hwfull) (hPN hzfull) hwz)
      exact (congrArg Prod.snd hzw).symm.trans hw.2
    · intro ht
      exact ⟨P.map z,⟨z,⟨hz.1,ht⟩,rfl⟩,rfl⟩
  change _ ↔ (H _ : G × ℝ).1 ∈ _ ∧ (H _ : G × ℝ).2 = _
  rw [hmem,hHval z hz]
  have hbasepoint := (H ⟨F (P.map z),⟨P.map z,⟨z,hz,rfl⟩,rfl⟩⟩).property.1
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, and_iff_right hbasepoint] <;> constructor <;> intro h <;> linarith

end PoincareConjecture.M76.OriginalDiskProduct
