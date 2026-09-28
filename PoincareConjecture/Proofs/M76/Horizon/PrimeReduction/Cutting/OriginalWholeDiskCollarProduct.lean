import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalOppositeDiskCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.WholeDiskProductOnOppositeDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.OriginalUnitDiskParameter









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem ChartwisePLSphere.exists_original_whole_disk_collar_product
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S U V : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (j : E → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjR : MapsTo j d (interior R))
    (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (hV : IsOpen V) (hjV : j '' d ⊆ V) :
    ∃ (t : Finset R) (N : SimplicialComplex ℝ (t → ℝ × V3))
      (C : (t → ℝ × V3) × ℝ → X) (K B : Set X)
      (H : Disk ≃ₜ d) (k : V2 → X)
      (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) k),
      N.faces.Finite ∧ PolyhedralPLInCharts e C (N.space ×ˢ I) ∧
      InjOn C (N.space ×ˢ I) ∧
      K = C '' (N.space ×ˢ J) ∧
      S = C '' (N.space ×ˢ ({1 / 2} : Set ℝ)) ∧
      B = C '' (N.space ×ˢ ({-(1 / 2)} : Set ℝ)) ∧
      IsCompact K ∧ IsConnected K ∧ PLDomain e K ∧ K ⊆ U ∩ interior R ∧
      Nonempty (ChartwisePLSphere e B) ∧ Disjoint B S ∧ frontier K = B ∪ S ∧
      H.IsFinitePL ∧ (∀ z : Disk, k z = j (H z)) ∧
      k '' Disk = j '' d ∧ k '' Rim = j '' q ∧
      MapsTo P.map (Disk ×ˢ I) (V ∩ interior R ∩ Bᶜ) ∧
      (∀ z ∈ Disk ×ˢ I, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
      IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹' P.openStrip) ∧
      IsCompact P.cutCarrier ∧ PLDomain e P.cutCarrier ∧
      P.closedStrip ∩ K = P.map '' (Rim ×ˢ J) ∧
      IsCompact (K ∪ P.closedStrip) ∧ PLDomain e (K ∪ P.closedStrip) ∧
      frontier (K ∪ P.closedStrip) = (frontier K \ P.openStrip) ∪ P.endDisks ∧
      (∀ η : ℝ, 0 < η → η ≤ 1 →
        IsOpen ((Subtype.val : (R ∩ (interior K)ᶜ : Set X) → X) ⁻¹'
          (P.map '' (Disk ×ˢ Ioo (-η) η))) ∧
        IsOpen ((Subtype.val : S → X) ⁻¹'
          (P.map '' (Rim ×ˢ Ioo (-η) η)))) ∧
      ∃ (c : (t → ℝ × V3) × ℝ → X) (ε : ℝ) (positive : Bool),
        PolyhedralPLInCharts e c (N.space ×ˢ I) ∧ InjOn c (N.space ×ˢ I) ∧
        0 < ε ∧ ε ≤ 1 / 4 ∧ IsConnected N.space ∧
        S = c '' (N.space ×ˢ ({0} : Set ℝ)) ∧
        MapsTo c (N.space ×ˢ Icc (-ε) ε) (U ∩ interior R) ∧
        IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) ∧
        K = c '' (N.space ×ˢ (if positive then Icc (-ε) 0 else Icc 0 ε)) ∧
        interior K = c '' (N.space ×ˢ (if positive then Ioo (-ε) 0 else Ioo 0 ε)) ∧
        ∃ F : X → (t → ℝ × V3),
          (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
          InjOn F S ∧ N.space = F '' S := by
  obtain ⟨H,k,hH,hk,hki,hkval,hkrim,hkd,hkq⟩ :=
    exists_original_unit_disk_parameter hd j hj hji
  obtain ⟨t,N,C,K,B,hN,hC,hCi,hCK,hCS,hCB,hK,hKPL,hKU,hB,hBS,hfront,hcontact,hraw⟩ :=
    s.exists_original_opposite_finite_disk_collar hR he hSR hU hSU hd j hj.continuousOn hproper
  have hkR : MapsTo k Disk (interior R) := by
    intro z hz
    rw [hkval ⟨z,hz⟩]
    exact hjR (H ⟨z,hz⟩).property
  have hkproper (z : V2) (hz : z ∈ Disk) : k z ∈ S ↔ z ∈ Rim := by
    rw [hkval ⟨z,hz⟩,hproper _ (H ⟨z,hz⟩).property]
    exact (hkrim ⟨z,hz⟩).symm
  have hkcontact : K ∩ (k '' Disk) = k '' Rim := by rwa [hkd,hkq]
  obtain ⟨sB⟩ := hB
  obtain ⟨P,hPsmall,hPmark,hopen,hcut,hcutPL,hstrip,hD,hDPL,hDfront,hwidths⟩ :=
    exists_whole_disk_product_on_opposite_domain hR he hK hKPL
      (fun x hx => (hKU hx).2) sB hBS hfront hkcontact hk hki hkR hkproper
      hV (hkd ▸ hjV)
  have hKc : IsConnected K := by
    obtain ⟨c,ε,positive,hc,_,hε,hεsmall,hNc,_,_,_,hKeq,_⟩ := hraw
    rw [hKeq]
    have hI : IsConnected (if positive then Icc (-ε) 0 else Icc 0 ε) := by
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
        exact isConnected_Icc (by linarith)
    apply (hNc.prod hI).image _
    apply hc.continuousOn.mono (prod_mono subset_rfl ?_)
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;>
      exact Icc_subset_Icc (by linarith) (by linarith)
  exact ⟨t,N,C,K,B,H,k,P,hN,hC,hCi,hCK,hCS,hCB,hK,hKc,hKPL,hKU,⟨sB⟩,
    hBS,hfront,hH,hkval,hkd,hkq,hPsmall,hPmark,hopen,hcut,hcutPL,hstrip,
    hD,hDPL,hDfront,hwidths,hraw⟩

end PoincareConjecture.M76
