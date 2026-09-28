import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreDecrease
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyCocoreGerm
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreCrossingTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyPrescribedExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyCenteredExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PrescribedProductCircleGeometry










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_family_noL3_cocore_step
    {X E ι κ : Type*} [MetricSpace X] [Finite κ] [DecidableEq κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R Q₀ : Set X}
    (O₀ S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (hR : IsCompact R) (he : PLDomain e R) (hSR : ∀ i, S i ⊆ interior R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    (hJcv : Convex ℝ J.space) (hJR : MapsTo Q.symm J.space (interior R))
    (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    (hpres : HasDisjointPolygonPresentation
      ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}))
    (hinside : ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) ⊆ interior J.space)
    (hcross : ∀ w ∈ (Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t},
      ∀ V : Set V3, IsOpen V → w ∈ V → ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ V ∩ interior J.space ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, (H x).2 - t = (B x).1.1)
    (hne : ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}).Nonempty) :
    ∃ (S' : κ → Set X) (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
      Pairwise (fun i j => Disjoint (S' i) (S' j)) ∧ (∀ i, S' i ⊆ interior R) ∧
      (⋃ i, S' i) ⊆ (⋃ i, S i) ∪ Q.symm '' interior J.space ∧
      HasDisjointPolygonPresentation
        ((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) ∧
      ((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) ⊆
        ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) ∧
      Nat.card (ConnectedComponents ↥((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t})) <
        Nat.card (ConnectedComponents ↥((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t})) ∧
      (∀ w ∈ (Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t},
        ∀ V : Set V3, IsOpen V → w ∈ V → ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ V ∩ interior J.space ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S' i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, (H x).2 - t = (B x).1.1) ∧
      ∃ (O' : κ → Set X) (W' : ∀ i, (S' i × unitInterval) ≃ₜ closure (O' i))
        (B' : κ × Bool → Set X) (_sB' : ∀ i, ChartwisePLSphere e (B' i)),
        (∀ i, IsOpen (O' i) ∧ closure (O' i) ⊆ interior R) ∧
        Pairwise (fun i j => Disjoint (closure (O' i)) (closure (O' j))) ∧
        (∀ i z, (W' i z : X) ∈ O' i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ i z, (W' i z : X) ∈ S' i ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ i, S' i ⊆ closure (O' i)) ∧
        IsCompact (R \ ⋃ i, O' i) ∧ PLDomain e (R \ ⋃ i, O' i) ∧
        HasNoPuncturedSphereComponents e f (R \ ⋃ i, O' i) ∧
        Pairwise (fun i j => Disjoint (B' i) (B' j)) ∧
        (∀ i, B' i ⊆ closure (O' i.1)) ∧ frontier (R \ ⋃ i, O' i) = frontier R ∪ ⋃ i, B' i := by
  classical
  obtain ⟨i,n,L,rho,hLi,hL,hLS,hrem,hρ,hρi,hρJ,hρS,hρother,hρcaps,hρband⟩ :=
    exists_sphere_family_cocore_positioned_product_at_height S sS hdis he.cover Q hQ
      J hJ hJQ hJcv H t hpres hinside hcross hne
  let region := rho '' (Disk ×ˢ Icc (-1 : ℝ) 1)
  have hregionCompact : IsCompact region :=
    ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc).image_of_continuousOn hρ.continuousOn
  have hregionConn : IsConnected region :=
    ((isConnected_closedBall (x := (0 : V2)) zero_le_one).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))).image rho hρ.continuousOn
  have hregionR : region ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨y,hy,heq⟩ := hρJ hz
    exact heq ▸ hJR (interior_subset hy)
  have hmeet : (S i ∩ region).Nonempty := by
    let z : V2 := fun _ => 1
    have hz : z ∈ Rim := by simp [z]
    have ht0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    exact ⟨rho (z,0),(hρS _ ⟨sphere_subset_closedBall hz,ht0⟩).mpr hz,
      mem_image_of_mem rho ⟨sphere_subset_closedBall hz,ht0⟩⟩
  obtain ⟨Qcut,B,sB,O,W,a,hQeq,hQc,hQPL,hnoQ,hO,hOdis,hW,hWcenter,hSC,hfront,
      hBdis,hBsub,hCc,hCconn,hCPL,hSiC,hOiC,hregionC,Kopp,Bopp,P,k,q,b,caps,U,WU,σ,
      hKopp,hKoppPL,hKoppO,hPmap,hPinside,hPproper,hPopen,hk,hkd,hkcover,hcaps,
      hσ,hσval,hU,hUPL,hUsub,hUC,hcapU,hcapmark,hnoU,hnoGlobal⟩ :=
    hno.exists_relative_family_prescribed_product_noL3_exchange O₀ S W₀ hQ₀eq hQ₀ hQ₀PL
      hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis
      hR he hSR K g hf hg hgi hreal i hregionCompact hregionConn hregionR hρother hmeet
      rho hρ hρi (fun z hz => mem_image_of_mem rho hz) hρS
  let new : Bool → Set X := fun c => (sS i).map '' k c ∪ P.capDisk c
  let F := Q.symm '' (Q.target ∩ {x | (H x).2 = t})
  have hretContact (c : Bool) : ((sS i).map '' k c) ∩ P.closedStrip = P.capRimSet c :=
    (hk c).2.2.2.2.trans (hk c).2.2.2.1
  have hcapF (c : Bool) : Disjoint (P.capDisk c) F := by
    simpa only [OriginalDiskProduct.capDisk,hPmap] using hρcaps c
  have hbandF : (P.map '' (Rim ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩ F = Q.symm '' L.boundary ℝ := by
    simpa only [hPmap] using hρband
  obtain ⟨hnewdis,houtside,hdelete,_,hstrip⟩ := P.positioned_circle_contact_geometry
    (fun c => (sS i).map '' k c) hkd hretContact hkcover hPproper hcapF hbandF
  have hstripRegion : P.closedStrip ⊆ region := by
    rintro _ ⟨z,hz,rfl⟩
    rw [hPmap]
    exact mem_image_of_mem rho ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  have hstripOther (j : κ) (hji : j ≠ i) : Disjoint P.closedStrip (S j) :=
    (hρother j hji).mono_left hstripRegion
  have hnewsub (c : Bool) : new c ⊆ S i ∪ P.closedStrip := by
    rintro x (hx | hx)
    · left
      apply hkcover.subset
      left
      cases c
      · exact Or.inr hx
      · exact Or.inl hx
    · right
      apply P.endDisks_subset_closedStrip
      rw [P.endDisks_eq_capDisks]
      cases c
      · exact Or.inl hx
      · exact Or.inr hx
  have hnewOther (c : Bool) (j : κ) (hji : j ≠ i) : Disjoint (new c) (S j) :=
    ((hdis hji.symm).union_left (hstripOther j hji)).mono_left (hnewsub c)
  have hfamilySub : (⋃ j, Function.update S i (new b) j) ⊆
      (⋃ j, S j) ∪ Q.symm '' interior J.space := by
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · subst j
      rw [Function.update_self] at hj
      rcases hnewsub b hj with hs | hs
      · exact Or.inl (mem_iUnion.mpr ⟨i,hs⟩)
      · obtain ⟨z,hz,rfl⟩ := hstripRegion hs
        exact Or.inr (hρJ hz)
    · rw [Function.update_of_ne hji] at hj
      exact Or.inl (mem_iUnion.mpr ⟨j,hj⟩)
  let height : V3 →ᴬ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  have hLS' : L.boundary ℝ ⊆ (Q '' (S i ∩ Q.source) ∩ J.space) ∩ {x | height x = t} :=
    fun _ hx => ⟨⟨(hLS hx).1.1,interior_subset (hLS hx).1.2⟩,(hLS hx).2⟩
  obtain ⟨hpres',hlt,hsubset⟩ := sphere_family_cocore_decrease S sS hdis i Q hQ J hJ hJQ
    height t hpres L hLi hL hLS' hrem new caps hnewdis hnewOther hdelete b
  have hnewLevel (c : Bool) : Disjoint (new c ∩ F) P.closedStrip := by
    apply disjoint_left.mpr
    rintro x ⟨hx,hxF⟩ hxStrip
    rcases hx with hx | hx
    · exact disjoint_left.mp (hcapF c)
        (P.capRimSet_subset_capDisk c ((hretContact c).subset ⟨hx,hxStrip⟩)) hxF
    · exact disjoint_left.mp (hcapF c) hx hxF
  obtain ⟨V,hV,hnewV,hagree⟩ := sphere_family_open_germ_after_exchange S i hdis new
    (fun c => (caps c).isCompact.isClosed) hnewdis P.closedStrip F hstrip.isClosed
    hstripOther houtside hnewsub hnewLevel b
  have hcross' := cocore_crossing_charts_of_open_agreement Q hJQ height.toAffineMap t
    hV hnewV hagree hcross
  obtain ⟨Oc,Hc,sS',W',B',sB',_,_,_,_,hO',hOdis',hW',hWcenter',hSC',_,hSdis',
      hCut',hCutPL',hno',hBdis',hBsub',hfront'⟩ :=
    hnoGlobal.exists_fixed_relative_family_centered_exchange O S W hR he
      (hQeq ▸ hQPL) (fun k => (hO k).1) (fun k => (hO k).2.2.2) hOdis hW hWcenter hSC
      sS B sB hBdis hBsub (hQeq ▸ hfront) i a hCc hCPL (caps b) WU σ hσ hσval b
      (hcapU.trans hU.isClosed.frontier_subset) hUC hcapmark hnoU K g hf hg hgi hreal
  exact ⟨Function.update S i (new b),sS',hSdis',fun j x hx => (hO' j).2 (hSC' j hx),
    hfamilySub,hpres',hsubset,hlt,hcross',Function.update O i Oc,W',B',sB',hO',hOdis',hW',hWcenter',hSC',
    hCut',hCutPL',hno',hBdis',hBsub',hfront'⟩

end PoincareConjecture.M76
