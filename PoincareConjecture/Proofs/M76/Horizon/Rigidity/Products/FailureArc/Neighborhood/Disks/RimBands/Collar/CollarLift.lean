import PoincareConjecture.Proofs.M76.Rigidity.OriginalBandCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.LateralArms



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_interval_band_width
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (hR : IsClosed R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    {F : P2 → X} (hF : ContinuousOn F (parameter 1))
    (hfront : MapsTo F (parameter 1) (frontier R))
    (a : ℝ → V2) (ha : MapsTo a J Rim)
    (hcenter : ∀ t ∈ J, F (0,t) = j (a t)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ MapsTo F (parameter ε)
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
  let f : J × I → R := fun z =>
    ⟨F ((z.2 : ℝ),(z.1 : ℝ)),hR.frontier_subset (hfront ⟨z.2.property,z.1.property⟩)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact hF.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
      (fun z => ⟨z.2.property,z.1.property⟩)
  have hzero (t : J) : f (t,⟨0,by norm_num⟩) ∈
      (Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
    refine ⟨(a t,0),⟨sphere_subset_closedBall (ha t.property),by norm_num⟩,?_⟩
    exact (P.central _ (sphere_subset_closedBall (ha t.property))).trans
      (hcenter t t.property).symm
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨ε,hε,hεsmall,hthin⟩ := hf.exists_closed_strip_subset hopen hzero
  refine ⟨ε,hε,hεsmall,?_⟩
  intro p hp
  have hpI : p.1 ∈ I := ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  exact hthin ⟨p.2,hp.2⟩ ⟨p.1,hpI⟩ (abs_le.mpr hp.1)

theorem exists_interval_band_lift
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    {F : P2 → X} (hF : PolyhedralPLInCharts e F (parameter 1))
    (hFi : InjOn F (parameter 1)) (hfront : MapsTo F (parameter 1) (frontier R))
    (a : ℝ → V2) (ha : MapsTo a J Rim)
    (hcenter : ∀ t ∈ J, F (0,t) = j (a t))
    (hzero : ∀ p ∈ parameter 1, F p ∈ j '' Disk ↔ p.1 = 0) :
    ∃ (ε : ℝ) (k : X → E), 0 < ε ∧ ε ≤ 1 / 2 ∧
      ContinuousOn k (P.map '' (Disk ×ˢ I)) ∧
      (∀ z ∈ Disk ×ˢ I, k (P.map z) = z) ∧
      (∀ y ∈ P.map '' (Disk ×ˢ I), P.map (k y) = y) ∧
      FinitePiecewiseAffineOn (k ∘ F) (parameter ε) ∧
      InjOn (k ∘ F) (parameter ε) ∧
      MapsTo (k ∘ F) (parameter ε) (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ t ∈ J, k (F (0,t)) = (a t,0)) ∧
      (∀ p ∈ parameter ε, P.map (k (F p)) = F p) ∧
      (∀ p ∈ parameter ε, (k (F p)).2 = 0 ↔ p.1 = 0) := by
  obtain ⟨ε,hε,hεsmall,hband⟩ := exists_interval_band_width P he.closed hopen
    hF.continuousOn hfront a ha hcenter
  obtain ⟨k,hkc,hleft,hback,hkmap⟩ := P.embedding.isEmbedding.exists_inverse_on_image
  have hfull : parameter ε ⊆ parameter 1 := fun p hp =>
    ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩
  have hhalf : Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ Disk ×ˢ I := fun p hp =>
    ⟨hp.1,⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩⟩
  have hFP : MapsTo F (parameter ε) (P.map '' (Disk ×ˢ I)) :=
    fun p hp => image_mono hhalf (hband hp)
  have hq : ContinuousOn (k ∘ F) (parameter ε) :=
    hkc.comp (hF.continuousOn.mono hfull) hFP
  have hball := (isFinitePLBallPair_Icc (by linarith : -ε < ε)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have hPq : PolyhedralPLInCharts e (P.map ∘ (k ∘ F)) K.space :=
    (hF.restrict_finite K hK (hKs.subset.trans hfull)).congr
      (fun p hp => (hback _ (hFP (hKs.subset hp))).symm)
  have hqPL := P.polyhedral.finitePiecewiseAffineOn_lift he.compatible P.injective
    K hK (hKs.symm ▸ hq) (fun p hp => hkmap (hFP (hKs.subset hp))) hPq
  have hqPL' : FinitePiecewiseAffineOn (k ∘ F) (parameter ε) := by
    simpa only [hKs,parameter,Function.comp_def] using hqPL
  have hcoord : MapsTo (k ∘ F) (parameter ε) (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro p hp
    obtain ⟨w,hw,hwF⟩ := hband hp
    change k (F p) ∈ _
    rw [← hwF,hleft w (hhalf hw)]
    exact ⟨(P.proper w (hhalf hw)).mp (hwF.symm ▸ hfront (hfull hp)),hw.2⟩
  have hcentral (t : ℝ) (ht : t ∈ J) : k (F (0,t)) = (a t,0) := by
    rw [hcenter t ht,← P.central _ (sphere_subset_closedBall (ha ht))]
    exact hleft _ ⟨sphere_subset_closedBall (ha ht),by norm_num⟩
  refine ⟨ε,k,hε,hεsmall,hkc,hleft,hback,hqPL',?_,hcoord,hcentral,
    fun p hp => hback _ (hFP hp),?_⟩
  · intro p hp q hq heq
    apply hFi (hfull hp) (hfull hq)
    exact (hback _ (hFP hp)).symm.trans
      ((congrArg P.map heq).trans (hback _ (hFP hq)))
  · intro p hp
    constructor
    · intro ht
      apply (hzero p (hfull hp)).mp
      have hc := hcoord hp
      refine ⟨(k (F p)).1,sphere_subset_closedBall hc.1,?_⟩
      have heq : ((k (F p)).1,(0 : ℝ)) = k (F p) := Prod.ext rfl ht.symm
      exact (P.central _ (sphere_subset_closedBall hc.1)).symm.trans
        ((congrArg P.map heq).trans (hback _ (hFP hp)))
    · intro hp0
      have heq : p = (0,p.2) := Prod.ext hp0 rfl
      rw [heq,hcentral _ hp.2]

end PoincareConjecture.M76.Dehn.Annuli.RimBands
