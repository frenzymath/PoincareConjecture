import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalExteriorAnnulusDisks
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalCollarSphereCoordinates
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.OriginalFinitePLBallImage

/-!
# Actual collar balls sharing the exterior disk annulus

The retained sphere disks are extended through the identical old collar.
Each resulting original PL ball meets the exterior strip in its whole
lateral annulus. Both complementary disk caps and their original rims
are retained, rather than postulated as a separate gluing package.
-/

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareMT.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_same_collar_annulus_balls
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R H K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (sB : ∀ b, ChartwisePLSphere e (B b))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hdis : Disjoint (B false) (B true))
    (hR : R = H ∩ (interior K)ᶜ) (hK : frontier K = B false ∪ B true)
    (hsmall : MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (interior H))
    (hstripK : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (N.space ×ˢ Icc (-1 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1)
    (hKeq : K = c '' (N.space ×ˢ Icc (-ε) ε))
    (hBeq : ∀ a, B a = c '' (N.space ×ˢ {if a then ε else -ε})) :
    ∃ (owner : Bool) (F : V3 × ℝ → X) (g : P2 → V3)
      (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ)),
      PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧ InjOn F (Sphere ×ˢ I) ∧
      F '' (Sphere ×ˢ I) = K ∧
      (∀ x ∈ Sphere, F (x,1) = (sB owner).map x) ∧
      F '' ((g '' Annulus) ×ˢ {(1 : ℝ)}) = P.map '' (Rim ×ˢ J) ∧
      ∀ b,
        let A := Sphere \ (k b \ q b)
        IsFinitePLBallPair P2 A (q b) ∧ k (!b) ∪ (g '' Annulus) = A ∧
        IsFinitePLBallPair P2 (C b) (q b ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P2 (k (!b) ×ˢ {(1 : ℝ)}) (q (!b) ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P3 (A ×ˢ I)
          (((g '' Annulus) ×ˢ {(1 : ℝ)}) ∪ (C b ∪ (k (!b) ×ˢ {(1 : ℝ)}))) ∧
        Nonempty (ChartwisePLBall e (F '' (A ×ˢ I))
          ((P.map '' (Rim ×ˢ J)) ∪ ((F '' C b) ∪ (F '' (k (!b) ×ˢ {(1 : ℝ)}))))) ∧
        (F '' (A ×ˢ I)) ∩ P.closedStrip = P.map '' (Rim ×ˢ J) ∧
        (F '' C b) ∩ (P.map '' (Rim ×ˢ J)) =
          P.map '' (Rim ×ˢ {if b then (1/2 : ℝ) else -(1/2)}) ∧
        (F '' (k (!b) ×ˢ {(1 : ℝ)})) ∩ (P.map '' (Rim ×ˢ J)) =
          P.map '' (Rim ×ˢ {if !b then (1/2 : ℝ) else -(1/2)}) ∧
        Disjoint (F '' (k (!b) ×ˢ {(1 : ℝ)})) (F '' C b) := by
  obtain ⟨owner,g,k,q,C,_,_,hgS,hgimage,hk,_,_,hprod⟩ :=
    P.exists_exterior_annulus_disks B sB hcompat hdis hR hK hsmall
  obtain ⟨F,hF,hFi,hFimage,hFtop,_⟩ := (sB owner).exists_same_collar_coordinates
    hcompat N hN c hc hci hε hεle owner (hBeq owner)
  have hFimage' : F '' (Sphere ×ˢ I) = K := hFimage.trans hKeq.symm
  have htop (A : Set V3) (hA : A ⊆ Sphere) :
      F '' (A ×ˢ {(1 : ℝ)}) = (sB owner).map '' A := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have ht1 : t = 1 := ht
      subst t
      exact ⟨z,hz,(hFtop z (hA hz)).symm⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(z,1),⟨hz,rfl⟩,hFtop z (hA hz)⟩
  have hbandS : g '' Annulus ⊆ Sphere := by rintro _ ⟨z,hz,rfl⟩; exact hgS hz
  have hband := (htop (g '' Annulus) hbandS).trans hgimage
  have hbandSI : (g '' Annulus) ×ˢ {(1 : ℝ)} ⊆ Sphere ×ˢ I :=
    prod_mono hbandS (by intro t ht; rw [show t=1 from ht]; norm_num)
  refine ⟨owner,F,g,k,q,C,hF,hFi,hFimage',hFtop,hband,?_⟩
  intro b
  obtain ⟨hA,hAeq,hC,hcap,hball,hmeet,hcapmeet,hcapdis⟩ := hprod b
  let A := Sphere \ (k b \ q b)
  have hASI : A ×ˢ I ⊆ Sphere ×ˢ I := prod_mono sdiff_subset subset_rfl
  have hbandA : g '' Annulus ⊆ A := subset_union_right.trans hAeq.subset
  have hbandAI : (g '' Annulus) ×ˢ {(1 : ℝ)} ⊆ A ×ˢ I :=
    prod_mono hbandA (by intro t ht; rw [show t=1 from ht]; norm_num)
  have hCA : C b ⊆ A ×ˢ I :=
    (subset_union_left.trans subset_union_right).trans hball.1
  have hcapA : k (!b) ×ˢ {(1 : ℝ)} ⊆ A ×ˢ I :=
    (subset_union_right.trans subset_union_right).trans hball.1
  have hballOriginal := exists_chartwisePLBall_image hball
    (ContinuousLinearEquiv.ofFinrankEq (by simp) : P3 ≃L[ℝ] V3) hF hASI hFi
  have hphysical : Nonempty (ChartwisePLBall e (F '' (A ×ˢ I))
      ((P.map '' (Rim ×ˢ J)) ∪ ((F '' C b) ∪ (F '' (k (!b) ×ˢ {(1 : ℝ)}))))) := by
    simpa only [image_union,hband] using hballOriginal
  have hballK : F '' (A ×ˢ I) ⊆ K := (image_mono hASI).trans hFimage'.subset
  have hbandBall : P.map '' (Rim ×ˢ J) ⊆ F '' (A ×ˢ I) :=
    hband.symm.subset.trans (image_mono hbandAI)
  refine ⟨hA,hAeq,hC,hcap,hball,hphysical,?_,?_,?_,?_⟩
  · apply Subset.antisymm
    · exact fun x hx => hstripK.subset ⟨hx.2,hballK hx.1⟩
    · exact fun x hx => ⟨hbandBall hx,(hstripK.symm.subset hx).1⟩
  · rw [← hband,← hFi.image_inter (hCA.trans hASI) hbandSI,hmeet,
      htop (q b) ((hk b).1.1.trans (hk b).2.1),(hk b).2.2.2.1]
  · rw [← hband,← hFi.image_inter (hcapA.trans hASI) hbandSI,hcapmeet,
      htop (q (!b)) ((hk (!b)).1.1.trans (hk (!b)).2.1),(hk (!b)).2.2.2.1]
  · apply disjoint_left.mpr
    rintro x ⟨u,hu,rfl⟩ ⟨v,hv,hvu⟩
    exact disjoint_left.mp hcapdis hu
      (hFi (hCA.trans hASI hv) (hcapA.trans hASI hu) hvu ▸ hv)

end PoincareMT.M76.OriginalDiskProduct
