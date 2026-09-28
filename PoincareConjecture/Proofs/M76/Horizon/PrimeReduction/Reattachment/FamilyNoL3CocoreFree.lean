import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.FamilyNoL3CocoreStep







set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_family_noL3_cocore_free
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
        ∀ x ∈ B.source, (H x).2 - t = (B x).1.1) :
    ∃ (S' : κ → Set X) (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
      Pairwise (fun i j => Disjoint (S' i) (S' j)) ∧ (∀ i, S' i ⊆ interior R) ∧
      (⋃ i, S' i) ⊆ (⋃ i, S i) ∪ Q.symm '' interior J.space ∧
      ((Q '' ((⋃ i, S' i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) = ∅ ∧
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
  induction hn : Nat.card (ConnectedComponents ↥
      ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}))
      using Nat.strong_induction_on generalizing S Q₀ O₀ B₀ with
  | h m ih =>
    by_cases hempty :
        ((Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t}) = ∅
    · exact ⟨S,sS,hdis,hSR,subset_union_left,hempty,
        O₀,W₀,B₀,sB₀,(fun i => ⟨hO₀ i,hCR₀ i⟩),hdis₀,hopen₀,hcenter₀,hSC₀,
        hQ₀eq ▸ hQ₀,hQ₀eq ▸ hQ₀PL,hQ₀eq ▸ hno,hB₀dis,hB₀sub,hQ₀eq ▸ hfront₀⟩
    · obtain ⟨S1,sS1,hdis1,hSR1,hsupport1,hpres1,hsection1,hlt,hcross1,
        O1,W1,B1,sB1,hO1,hOdis1,hW1,hWcenter1,hSC1,hCut1,hCutPL1,hno1,
        hBdis1,hBsub1,hfront1⟩ :=
        exists_family_noL3_cocore_step O₀ S sS hdis W₀ hQ₀eq hQ₀ hQ₀PL
          hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hno
          hR he hSR K g hf hg hgi hreal Q hQ J hJ hJQ hJcv hJR H t
          hpres hinside hcross (Set.nonempty_iff_ne_empty.mpr hempty)
      obtain ⟨S2,sS2,hdis2,hSR2,hsupport2,hfree2,hcut2⟩ :=
        ih (Nat.card (ConnectedComponents ↥
          ((Q '' ((⋃ i, S1 i) ∩ Q.source) ∩ J.space) ∩ {x | (H x).2 = t})))
          (by omega)
          (S := S1) (sS := sS1) (hdis := hdis1) (hSR := hSR1)
          (Q₀ := R \ ⋃ i, O1 i) (O₀ := O1) (W₀ := W1)
          (hQ₀eq := rfl) (hQ₀ := hCut1) (hQ₀PL := hCutPL1)
          (hO₀ := fun i => (hO1 i).1) (hCR₀ := fun i => (hO1 i).2)
          (hdis₀ := hOdis1) (hopen₀ := hW1) (hcenter₀ := hWcenter1) (hSC₀ := hSC1)
          (B₀ := B1) (sB₀ := sB1) (hB₀dis := hBdis1) (hB₀sub := hBsub1)
          (hfront₀ := hfront1) (hno := hno1)
          (hpres := hpres1) (hinside := hsection1.trans hinside) (hcross := hcross1) rfl
      refine ⟨S2,sS2,hdis2,hSR2,?_,hfree2,hcut2⟩
      intro x hx
      rcases hsupport2 hx with hx | hx
      · exact hsupport1 hx
      · exact Or.inr hx

end PoincareConjecture.M76

