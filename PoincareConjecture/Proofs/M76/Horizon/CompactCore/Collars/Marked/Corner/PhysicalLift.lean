import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.CollarLift

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_local_band_lift
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    {a b : ℝ} (hab : a < b) {F : P2 → X}
    (hF : PolyhedralPLInCharts e F (I ×ˢ Icc a b)) (hFi : InjOn F (I ×ˢ Icc a b))
    (hfront : MapsTo F (I ×ˢ Icc a b) (frontier R))
    (c : ℝ → V2) (hc : MapsTo c (Icc a b) Rim)
    (hcenter : ∀ s ∈ Icc a b, F (0, s) = j (c s))
    (hzero : ∀ p ∈ I ×ˢ Icc a b, F p ∈ j '' Disk ↔ p.1 = 0) :
    ∃ (w : ℝ) (q : P2 → E), 0 < w ∧ w ≤ 1 / 2 ∧
      FinitePiecewiseAffineOn q (Icc (-w) w ×ˢ Icc a b) ∧
      InjOn q (Icc (-w) w ×ˢ Icc a b) ∧
      MapsTo q (Icc (-w) w ×ˢ Icc a b) (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ s ∈ Icc a b, q (0, s) = (c s, 0)) ∧
      (∀ p ∈ Icc (-w) w ×ˢ Icc a b, P.map (q p) = F p) ∧
      ∀ p ∈ Icc (-w) w ×ˢ Icc a b, (q p).2 = 0 ↔ p.1 = 0 := by
  let f : Icc a b × I → R := fun z =>
    ⟨F ((z.2 : ℝ), (z.1 : ℝ)), he.closed.frontier_subset (hfront ⟨z.2.property, z.1.property⟩)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact hF.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)) (fun z => ⟨z.2.property, z.1.property⟩)
  have hbase (s : Icc a b) : f (s, ⟨0, by norm_num⟩) ∈
      (Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
    refine ⟨(c s, 0), ⟨sphere_subset_closedBall (hc s.property), by norm_num⟩, ?_⟩
    exact (P.central _ (sphere_subset_closedBall (hc s.property))).trans (hcenter s s.property).symm
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨w, hw, hwsmall, hthin⟩ := hf.exists_closed_strip_subset hopen hbase
  have hfull : Icc (-w) w ×ˢ Icc a b ⊆ I ×ˢ Icc a b := fun p hp =>
    ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hband : MapsTo F (Icc (-w) w ×ˢ Icc a b)
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
    intro p hp
    exact hthin ⟨p.2, hp.2⟩ ⟨p.1, (hfull hp).1⟩ (abs_le.mpr hp.1)
  have hhalf : Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ Disk ×ˢ I := fun p hp =>
    ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hFP : MapsTo F (Icc (-w) w ×ˢ Icc a b) (P.map '' (Disk ×ˢ I)) :=
    fun _ hp => image_mono hhalf (hband hp)
  obtain ⟨k, hkc, hleft, hback, hkmap⟩ := P.embedding.isEmbedding.exists_inverse_on_image
  have hq : ContinuousOn (k ∘ F) (Icc (-w) w ×ˢ Icc a b) :=
    hkc.comp (hF.continuousOn.mono hfull) hFP
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (by linarith : -w < w)).prod (isFinitePLBallPair_Icc hab)
  have hPq : PolyhedralPLInCharts e (P.map ∘ (k ∘ F)) K.space :=
    (hF.restrict_finite K hK (hKs.subset.trans hfull)).congr
      (fun p hp => (hback _ (hFP (hKs.subset hp))).symm)
  have hqPL := P.polyhedral.finitePiecewiseAffineOn_lift he.compatible P.injective
    K hK (hKs.symm ▸ hq) (fun p hp => hkmap (hFP (hKs.subset hp))) hPq
  have hcoord : MapsTo (k ∘ F) (Icc (-w) w ×ˢ Icc a b)
      (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro p hp
    obtain ⟨z, hz, hzF⟩ := hband hp
    change k (F p) ∈ _
    rw [← hzF, hleft z (hhalf hz)]
    exact ⟨(P.proper z (hhalf hz)).mp (hzF.symm ▸ hfront (hfull hp)), hz.2⟩
  have hcentral (s : ℝ) (hs : s ∈ Icc a b) : k (F (0, s)) = (c s, 0) := by
    rw [hcenter s hs, ← P.central _ (sphere_subset_closedBall (hc hs))]
    exact hleft _ ⟨sphere_subset_closedBall (hc hs), by norm_num⟩
  refine ⟨w, k ∘ F, hw, hwsmall, hKs ▸ hqPL, ?_, hcoord, hcentral,
    fun p hp => hback _ (hFP hp), ?_⟩
  · intro p hp z hz heq
    exact hFi (hfull hp) (hfull hz) ((hback _ (hFP hp)).symm.trans
      ((congrArg P.map heq).trans (hback _ (hFP hz))))
  · intro p hp
    constructor
    · intro ht
      apply (hzero p (hfull hp)).mp
      have hqc := hcoord hp
      refine ⟨(k (F p)).1, sphere_subset_closedBall hqc.1, ?_⟩
      have heq : ((k (F p)).1, (0 : ℝ)) = k (F p) := Prod.ext rfl ht.symm
      exact (P.central _ (sphere_subset_closedBall hqc.1)).symm.trans
        ((congrArg P.map heq).trans (hback _ (hFP hp)))
    · intro hp0
      have heq : p = (0, p.2) := Prod.ext hp0 rfl
      rw [heq]
      exact congrArg Prod.snd (hcentral p.2 hp.2)

end PoincareConjecture.M76
