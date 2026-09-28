import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskThreePorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CommonCutComponentDomains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorCapSpheres
import Mathlib.Data.Fin.VecNotation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalCollarExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereProductDomain
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_retained_collar_ball
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {F : V3 × ℝ → X}
    (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I))
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere) :
    Nonempty (ChartwisePLBall e (F '' (k ×ˢ I))
      (F '' ((q ×ˢ I) ∪ (k ×ˢ ({0, 1} : Set ℝ))))) := by
  exact exists_chartwisePLBall_image
    (hk.prod (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)))
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] V3)
    hF (prod_mono hkS subset_rfl) hFi

private theorem ball_reattachment_exterior
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {H bd W R : Set X}
    (hball : ChartwisePLBall e H bd) (hHR : H ⊆ R) (hmeet : W ∩ H ⊆ bd) :
    R ∩ (interior W)ᶜ = (R ∩ (interior (W ∪ H))ᶜ) ∪ H := by
  have hdis : Disjoint (interior W) (interior H) := by
    apply disjoint_left.mpr
    intro x hxW hxH
    have hxfront : x ∈ frontier H := hball.frontier_eq.symm ▸
      hmeet ⟨interior_subset hxW, interior_subset hxH⟩
    exact hxfront.2 hxH
  have havoid : Disjoint (interior W) H := by
    rw [← hball.closure_interior]
    exact hdis.closure_right isOpen_interior
  have hlocal : interior (W ∪ H) ∩ Hᶜ ⊆ interior W := by
    apply interior_maximal _ (isOpen_interior.inter hball.isCompact.isClosed.isOpen_compl)
    intro x hx
    exact (interior_subset hx.1).resolve_right hx.2
  apply Subset.antisymm
  · intro x hx
    by_cases hxH : x ∈ H
    · exact Or.inr hxH
    · exact Or.inl ⟨hx.1, fun h => hx.2 (hlocal ⟨h, hxH⟩)⟩
  · rintro x (hx | hx)
    · exact ⟨hx.1, fun h => hx.2 (interior_mono subset_union_left h)⟩
    · exact ⟨hHR hx, fun h => disjoint_left.mp havoid h hx⟩

theorem retained_collar_reattachment_geometry
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K B : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e B)
    (F : V3 × ℝ → X)
    (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere)
    (hcontact : (s.map '' k) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q)
    (b : Bool) (hrim : s.map '' q = P.capRimSet b) :
    let H := F '' (k ×ˢ I)
    let W := (F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip
    IsCompact H ∧
      H ∩ P.closedStrip = F '' (q ×ˢ {(1 : ℝ)}) ∧
      Disjoint H P.openStrip ∧
      W ∪ H = K ∪ P.closedStrip ∧
      W ∩ H = F '' (q ×ˢ I) := by
  classical
  let H := F '' (k ×ˢ I)
  let A := Sphere \ (k \ q)
  have hqS : q ⊆ Sphere := hk.1.trans hkS
  have hHsub : H ⊆ K := by
    rw [← hFK]
    exact image_mono (prod_mono hkS subset_rfl)
  have htopimage (t : Set V3) (ht : t ⊆ Sphere) :
      F '' (t ×ˢ {(1 : ℝ)}) = s.map '' t := by
    ext x
    constructor
    · rintro ⟨⟨z, u⟩, ⟨hz, hu⟩, rfl⟩
      have hu1 : u = 1 := hu
      subst u
      exact ⟨z, hz, (htop z (ht hz)).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z, 1), ⟨hz, rfl⟩, htop z (ht hz)⟩
  have hHstrip : H ∩ P.closedStrip = F '' (q ×ˢ {(1 : ℝ)}) := by
    rw [htopimage q hqS]
    apply Subset.antisymm
    · rintro x ⟨⟨⟨z, t⟩, ⟨hzk, ht⟩, rfl⟩, hxstrip⟩
      have hxband := hstripK.subset ⟨hxstrip, hHsub ⟨(z, t), ⟨hzk, ht⟩, rfl⟩⟩
      let y := s.parametrization.symm ⟨F (z, t), hband hxband⟩
      have hy : s.map y = F (z, t) :=
        (s.map_eq y).trans (congrArg Subtype.val (s.parametrization.apply_symm_apply _))
      have heq : (z, t) = ((y : V3), 1) := hFi ⟨hkS hzk, ht⟩
        ⟨y.property, by norm_num⟩ (hy.symm.trans (htop y y.property).symm)
      have ht1 : t = 1 := congrArg Prod.snd heq
      subst t
      apply hcontact.subset
      exact ⟨⟨z, hzk, (htop z (hkS hzk)).symm⟩, hxband⟩
    · intro x hx
      have hxret := hcontact.symm.subset hx
      have hxH : x ∈ H := by
        rw [← htopimage q hqS] at hx
        exact image_mono (prod_mono hk.1 (by intro t ht; rcases ht with rfl; norm_num)) hx
      exact ⟨hxH, (hstripK.symm.subset hxret.2).1⟩
  have hopen_sub : P.openStrip ⊆ P.closedStrip := by
    exact image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have havoid : Disjoint H P.openStrip := by
    apply disjoint_left.mpr
    intro x hxH hxopen
    have hxrim := hHstrip.subset ⟨hxH, hopen_sub hxopen⟩
    rw [htopimage q hqS, hrim] at hxrim
    have hxend : x ∈ P.endDisks := (P.capRimSet_subset_capDisk b).trans (by
      rw [P.endDisks_eq_capDisks]
      cases b
      · exact subset_union_left
      · exact subset_union_right) hxrim
    exact (P.closedStrip_sdiff_openStrip.symm ▸ hxend).2 hxopen
  have hAk : A ∪ k = Sphere := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact hz.1
      · exact hkS hz
    · intro hz
      by_cases hzk : z ∈ k
      · exact Or.inr hzk
      · exact Or.inl ⟨hz, fun h => hzk h.1⟩
  have hAkq : A ∩ k = q := by
    ext z
    constructor
    · intro hz
      by_contra hnot
      exact hz.1.2 ⟨hz.2, hnot⟩
    · exact fun hz => ⟨⟨hqS hz, fun h => h.2 hz⟩, hk.1 hz⟩
  have hWH : ((F '' (A ×ˢ I)) ∪ P.closedStrip) ∪ H = K ∪ P.closedStrip := by
    rw [union_right_comm, ← image_union, ← union_prod, hAk, hFK]
  have hAH : (F '' (A ×ˢ I)) ∩ H = F '' (q ×ˢ I) := by
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, hzx⟩, ⟨w, hw, hwx⟩⟩
      have hzw : z = w := hFi ⟨hz.1.1, hz.2⟩ ⟨hkS hw.1, hw.2⟩ (hzx.trans hwx.symm)
      subst w
      exact ⟨z, ⟨hAkq.subset ⟨hz.1, hw.1⟩, hz.2⟩, hzx⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hza := hAkq.symm.subset hz.1
      exact ⟨⟨z, ⟨hza.1, hz.2⟩, rfl⟩, ⟨z, ⟨hza.2, hz.2⟩, rfl⟩⟩
  refine ⟨(hk.isCompact.prod isCompact_Icc).image_of_continuousOn
    (hF.continuousOn.mono (prod_mono hkS subset_rfl)), hHstrip, havoid, hWH, ?_⟩
  rw [union_inter_distrib_right, hAH, inter_comm P.closedStrip H, hHstrip]
  apply union_eq_left.mpr
  exact image_mono (prod_mono subset_rfl (by intro t ht; rcases ht with rfl; norm_num))




theorem retained_collar_exchange_exterior
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K B : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e B)
    (F : V3 × ℝ → X)
    (hF : PolyhedralPLInCharts e F (Sphere ×ˢ I))
    (hFi : InjOn F (Sphere ×ˢ I)) (hFK : F '' (Sphere ×ˢ I) = K)
    (htop : ∀ z ∈ Sphere, F (z, 1) = s.map z)
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (hband : P.map '' (Rim ×ˢ J) ⊆ B)
    {k q : Set V3} (hk : IsFinitePLBallPair P2 k q) (hkS : k ⊆ Sphere)
    (hcontact : (s.map '' k) ∩ (P.map '' (Rim ×ˢ J)) = s.map '' q)
    (b : Bool) (hrim : s.map '' q = P.capRimSet b)
    (ambient : Set X) (hKambient : K ⊆ ambient) :
    let H := F '' (k ×ˢ I)
    let W := (F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip
    Nonempty (ChartwisePLBall e H (F '' ((q ×ˢ I) ∪ (k ×ˢ ({0, 1} : Set ℝ))))) ∧
      Disjoint H (interior W) ∧
      ambient ∩ (interior W)ᶜ =
        (ambient ∩ (interior (K ∪ P.closedStrip))ᶜ) ∪ H := by
  obtain ⟨hball⟩ := exists_retained_collar_ball hF hFi hk hkS
  obtain ⟨_, _, _, hunion, hmeet⟩ := P.retained_collar_reattachment_geometry
    s F hF hFi hFK htop hstripK hband hk hkS hcontact b hrim
  have hHsub : F '' (k ×ˢ I) ⊆ ambient :=
    (image_mono (prod_mono hkS subset_rfl)).trans (hFK.subset.trans hKambient)
  have hcontact' : ((F '' ((Sphere \ (k \ q)) ×ˢ I)) ∪ P.closedStrip) ∩
      (F '' (k ×ˢ I)) ⊆ F '' ((q ×ˢ I) ∪ (k ×ˢ ({0, 1} : Set ℝ))) := by
    rw [hmeet]
    exact image_mono subset_union_left
  have heq := ball_reattachment_exterior hball hHsub hcontact'
  rw [hunion] at heq
  refine ⟨⟨hball⟩, ?_, heq⟩
  apply disjoint_left.mpr
  intro x hxH hxW
  have hx := heq.symm.subset (Or.inr hxH)
  exact hx.2 hxW

end PoincareConjecture.M76.OriginalDiskProduct
